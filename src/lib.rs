pub mod conversion_utils;
pub mod db;

use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    str::FromStr,
    sync::{Arc, Mutex},
};

use conversion_utils::{b160_to_h160, h256_to_b256};
use era_test_node::{
    fork::{ForkDetails, ForkSource},
    node::InMemoryNode,
};
use revm::{
    primitives::{
        Account, AccountInfo, Bytecode, Bytes, EVMResult, Env, Eval, ExecutionResult,
        HashMap as rHashMap, ResultAndState, StorageSlot, TxEnv, B160, B256,
    },
    Database,
};
use vm::vm::VmTxExecutionResult;
use zksync_basic_types::{
    web3::signing::keccak256, L1BatchNumber, L2ChainId, MiniblockNumber, H160, H256, U256,
};
use zksync_types::{
    api::{BlockIdVariant, Transaction},
    fee::Fee,
    l2::L2Tx,
    transaction_request::PaymasterParams,
    StorageKey, StorageLogQueryType, ACCOUNT_CODE_STORAGE_ADDRESS,
};

use revm::primitives::U256 as revmU256;
use zksync_utils::{h256_to_account_address, h256_to_u256, u256_to_h256};

use crate::{
    conversion_utils::{h160_to_b160, h256_to_revm_u256, revm_u256_to_h256, u256_to_revm_u256},
    db::RevmDatabaseForEra,
};

fn contract_address_from_tx_result(execution_result: &VmTxExecutionResult) -> Option<H160> {
    for query in execution_result.result.logs.storage_logs.iter().rev() {
        if query.log_type == StorageLogQueryType::InitialWrite
            && query.log_query.address == ACCOUNT_CODE_STORAGE_ADDRESS
        {
            return Some(h256_to_account_address(&u256_to_h256(query.log_query.key)));
        }
    }
    None
}

fn limit_gas_more(gas_limit: U256) -> U256 {
    if gas_limit > U256::from(2147483640) {
        U256::from(2147483640)
    } else {
        gas_limit
    }
}

fn good_max_fee_per_gas(max_fee_per_gas: U256) -> U256 {
    if max_fee_per_gas < U256::from(260000000) {
        U256::from(260_000_000)
    } else {
        max_fee_per_gas
    }
}

/// Prepares calldata to invoke deployer contract.
/// This method encodes parameters for the `create` method.
pub fn encode_deploy_params_create(
    salt: H256,
    contract_hash: H256,
    constructor_input: Vec<u8>,
) -> Vec<u8> {
    // TODO (SMA-1608): We should not re-implement the ABI parts in different places, instead have the ABI available
    //  from the `zksync_contracts` crate.
    let signature = ethabi::short_signature(
        "create",
        &[
            ethabi::ParamType::FixedBytes(32),
            ethabi::ParamType::FixedBytes(32),
            ethabi::ParamType::Bytes,
        ],
    );
    let params = ethabi::encode(&[
        ethabi::Token::FixedBytes(salt.as_bytes().to_vec()),
        ethabi::Token::FixedBytes(contract_hash.as_bytes().to_vec()),
        ethabi::Token::Bytes(constructor_input),
    ]);

    signature.iter().copied().chain(params).collect()
}

fn ensure_chunkable(bytes: &[u8]) {
    assert!(
        bytes.len() % 32 == 0,
        "Bytes must be divisible by 32 to split into chunks"
    );
}

pub fn bytes_to_chunks(bytes: &[u8]) -> Vec<[u8; 32]> {
    ensure_chunkable(bytes);
    bytes
        .chunks(32)
        .map(|el| {
            let mut chunk = [0u8; 32];
            chunk.copy_from_slice(el);
            chunk
        })
        .collect()
}

pub fn hash_bytecode(code: &[u8]) -> H256 {
    let chunked_code = bytes_to_chunks(code);
    let hash = zk_evm::zkevm_opcode_defs::utils::bytecode_to_code_hash(&chunked_code)
        .expect("Invalid bytecode");

    H256(hash)
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
pub struct PackedEraBytecode {
    pub hash: String,
    pub bytecode: String,
    pub factory_deps: Vec<String>,
}

pub fn tx_env_to_era_tx(tx_env: TxEnv, nonce: u64) -> L2Tx {
    println!(
        "Creating transaction with nonce: {:?} from: {:?}",
        tx_env.nonce, tx_env.caller
    );
    let mut l2tx = match tx_env.transact_to {
        revm::primitives::TransactTo::Call(contract_address) => L2Tx::new(
            contract_address.as_fixed_bytes().into(),
            tx_env.data.to_vec(),
            (tx_env.nonce.unwrap_or(nonce) as u32).into(),
            Fee {
                gas_limit: limit_gas_more(tx_env.gas_limit.into()),
                max_fee_per_gas: good_max_fee_per_gas(U256::from_little_endian(
                    tx_env.gas_price.as_le_slice(),
                )),
                max_priority_fee_per_gas: U256::from_little_endian(
                    tx_env.gas_priority_fee.unwrap_or_default().as_le_slice(),
                ),
                gas_per_pubdata_limit: U256::from(800),
            },
            tx_env.caller.as_fixed_bytes().into(),
            U256::from_little_endian(tx_env.value.as_le_slice()),
            None, // factory_deps
            PaymasterParams::default(),
        ),
        revm::primitives::TransactTo::Create(scheme) => {
            println!("Deploy - scheme is {:?}", scheme);

            let packed_bytecode: PackedEraBytecode =
                serde_json::from_slice(&tx_env.data.to_vec()).unwrap();

            //let packed_bytecodes = serde_json tx_env.data.to_vec();

            let bytecode = hex::decode(packed_bytecode.bytecode.clone()).unwrap();
            let bytecode_hash = hash_bytecode(&bytecode);
            let factory_deps: Vec<Vec<u8>> = packed_bytecode
                .factory_deps
                .iter()
                .chain([&packed_bytecode.bytecode])
                .map(|entry| hex::decode(entry).unwrap())
                .collect();

            assert_eq!(
                bytecode_hash,
                H256::from_str(&packed_bytecode.hash).unwrap()
            );
            println!("DEPLOY - factory deps length: {:?}", factory_deps.len());

            L2Tx::new(
                H160::from_low_u64_be(0x8006),
                // TODO: wrap tx_env.data !!
                encode_deploy_params_create(Default::default(), bytecode_hash, Default::default()),
                //tx_env.data.to_vec(),
                (tx_env.nonce.unwrap_or(nonce) as u32).into(),
                Fee {
                    gas_limit: limit_gas_more(tx_env.gas_limit.into()),
                    max_fee_per_gas: good_max_fee_per_gas(U256::from_little_endian(
                        tx_env.gas_price.as_le_slice(),
                    )),
                    max_priority_fee_per_gas: U256::from_little_endian(
                        tx_env.gas_priority_fee.unwrap_or_default().as_le_slice(),
                    ),
                    gas_per_pubdata_limit: U256::from(800),
                },
                tx_env.caller.as_fixed_bytes().into(),
                U256::from_little_endian(tx_env.value.as_le_slice()),
                Some(factory_deps), // factory_deps
                PaymasterParams::default(),
            )
        }
    };
    // TODO: hash is incorrect (data too)
    l2tx.set_input(
        tx_env.data.to_vec(),
        H256(keccak256(tx_env.data.to_vec().as_slice())),
    );
    l2tx
}

#[derive(Debug, Clone)]
pub enum DatabaseError {
    MissingCode(bool),
}

fn set_min_l1_gas_price(l1_gas_price: u64) -> u64 {
    if l1_gas_price == 0 {
        1000 as u64
    } else {
        l1_gas_price
    }
}

pub fn h256_to_h160(i: &H256) -> H160 {
    H160::from_slice(&i.0[12..32])
}

pub fn fetch_account_code<DB: Database>(
    account: H160,
    db: &mut DB,
    modified_keys: &HashMap<StorageKey, H256>,
    bytecodes: &HashMap<U256, Vec<U256>>,
) -> Option<Bytecode> {
    // First - check if the bytecode was set/changed in the recent block.

    let account_code_storage =
        b160_to_h160(B160::from_str("0x0000000000000000000000000000000000008002").unwrap());

    for (k, v) in modified_keys.iter() {
        // If there was a change in 'AccountCodeStorage' system contract.
        if k.account().address() == &account_code_storage && h256_to_h160(k.key()) == account {
            let new_bytecode_hash = v.clone();
            let new_bytecode = bytecodes.get(&h256_to_u256(new_bytecode_hash)).unwrap();
            let u8_bytecode: Vec<u8> = new_bytecode
                .iter()
                .flat_map(|x| u256_to_h256(x.clone()).to_fixed_bytes())
                //.cloned()
                .collect();

            return Some(Bytecode {
                bytecode: Bytes::copy_from_slice(&u8_bytecode.as_slice()),
                hash: h256_to_b256(new_bytecode_hash),
                state: revm::primitives::BytecodeState::Raw,
            });
        }
    }

    // this is super stupid and slow
    for (k, v) in bytecodes {
        if h256_to_h160(&u256_to_h256(k.clone())) == account {
            let u8_bytecode: Vec<u8> = v
                .iter()
                .flat_map(|x| u256_to_h256(x.clone()).to_fixed_bytes())
                //.cloned()
                .collect();

            return Some(Bytecode {
                bytecode: Bytes::copy_from_slice(&u8_bytecode.as_slice()),
                hash: h256_to_b256(u256_to_h256(*k)),
                state: revm::primitives::BytecodeState::Raw,
            });
        }
    }

    let b160_account = h160_to_b160(account);

    db.basic(b160_account)
        .ok()
        .map(|db_account| db_account.map(|x| x.code))
        .flatten()
        .flatten()
}

pub fn run_era_transaction<'a, DB, E, INSP>(
    env: &Env,
    db: &mut DB,
    inspector: INSP, //    db: &dyn Database<Error = DatabaseError>,
                     //    inspector: &mut dyn Inspector<dyn Database<Error = DatabaseError>>,
) -> EVMResult<E>
where
    DB: Database + Send + 'a,
    <DB as revm::Database>::Error: Debug,
{
    // TODO - pass chain_id from env.cfg_env
    // TODO: pass stuff from block env (block number etc) into fork.

    let foo = Arc::new(Mutex::new(Box::new(db)));
    let mut bar = RevmDatabaseForEra { db: foo };
    /*
    let num_and_ts = (&bar).get_storage_at(
        H160::from_str("0x000000000000000000000000000000000000800b").unwrap(),
        U256::from(7),
        None,
    );
    let ab1 = num_and_ts.unwrap();
    let bb = ab1.as_fixed_bytes();
    let num: [u8; 8] = bb[24..32].try_into().unwrap();
    let ts: [u8; 8] = bb[8..16].try_into().unwrap();

    let num = u64::from_be_bytes(num);
    let ts = u64::from_be_bytes(ts);
    */

    let (num, ts) = bar.block_number_and_timestamp();

    // FIXME: replace with proper call to fetch current nonce for account.
    let nonce_storage = (&bar).get_storage_at(
        H160::from_str("0x0000000000000000000000000000000000008003").unwrap(),
        U256::from_str("0x3e1a6e48cd7e8291e25c14adac8306b064f909d041e2dc71d7bda438c8681263")
            .unwrap(),
        None,
    );
    let nonces: [u8; 8] = nonce_storage.unwrap().as_fixed_bytes()[24..32]
        .try_into()
        .unwrap();

    let nonces = u64::from_be_bytes(nonces);

    println!(
        "*** Starting ERA transaction: block: {:?} timestamp: {:?} - but using {:?} and {:?} instead with nonce {:?}",
        env.block.number.to::<u32>(),
        env.block.timestamp.to::<u64>(),
        num,
        ts,
        nonces
    );

    let fork_details = ForkDetails {
        fork_source: &bar,
        l1_block: L1BatchNumber(num as u32), //L1BatchNumber(env.block.number.to::<u32>() - 1), // HACK
        l2_miniblock: num,                   //env.block.number.to::<u64>() - 1,
        block_timestamp: ts,                 //env.block.timestamp.to::<u64>(),
        overwrite_chain_id: Some(L2ChainId(env.cfg.chain_id.to::<u16>())),
        l1_gas_price: set_min_l1_gas_price(env.block.basefee.to::<u64>()),
    };

    let node = InMemoryNode::new(
        Some(fork_details),
        era_test_node::node::ShowCalls::All,
        era_test_node::node::ShowStorageLogs::All,
        era_test_node::node::ShowVMDetails::All,
        false,
        false,
    );

    // TODO: get nonce on your own (from the database).
    let l2_tx = tx_env_to_era_tx(env.tx.clone(), nonces);

    let era_execution_result = node
        .run_l2_tx_inner(
            l2_tx,
            vm::vm_with_bootloader::TxExecutionMode::VerifyExecute,
        )
        .unwrap();

    let (modified_keys, tx_result, block, bytecodes) = era_execution_result;
    let maybe_contract_address = contract_address_from_tx_result(&tx_result);

    let execution_result = match tx_result.status {
        zksync_types::tx::tx_execution_info::TxExecutionStatus::Success => {
            ExecutionResult::Success {
                reason: Eval::Return,
                gas_used: env.tx.gas_limit - tx_result.gas_refunded as u64,
                gas_refunded: tx_result.gas_refunded as u64,
                logs: vec![],
                output: revm::primitives::Output::Create(
                    Bytes::new(), // FIXME (function results)
                    maybe_contract_address.map(|address| h160_to_b160(address)),
                ),
            }
        }
        zksync_types::tx::tx_execution_info::TxExecutionStatus::Failure => {
            ExecutionResult::Revert {
                gas_used: env.tx.gas_limit - tx_result.gas_refunded as u64,
                output: Bytes::new(), // FIXME (function results)
            }
        }
    };
    //let state: State= Default::default();

    let account_to_keys: HashMap<H160, HashMap<StorageKey, H256>> =
        modified_keys
            .iter()
            .fold(HashMap::new(), |mut acc, (storage_key, value)| {
                acc.entry(*storage_key.address())
                    .or_insert_with(HashMap::new)
                    .insert(*storage_key, *value);
                acc
            });
    for (k, v) in account_to_keys.iter() {
        println!("Keys changed for {:?}", k);
        for (k1, v1) in v.iter() {
            println!("  index: {:?} value: {:?}", k1.key(), v1);
        }
    }

    // List of touched accounts
    let mut accounts_touched: HashSet<H160> = Default::default();
    // All accounts where storage was modified.
    for x in account_to_keys.keys() {
        accounts_touched.insert(x.clone());
    }
    // Also insert 'fake' accoutnts for bytecodes (to make sure that factory bytecodes get persisted).
    for (k, _) in &bytecodes {
        accounts_touched.insert(h256_to_h160(&u256_to_h256(*k)));
    }

    let account_code_storage =
        b160_to_h160(B160::from_str("0x0000000000000000000000000000000000008002").unwrap());
    // FIXME: also load stuff from database somehow.

    if let Some(account_bytecodes) = account_to_keys.get(&account_code_storage) {
        for (k, v) in account_bytecodes {
            let account_address = H160::from_slice(&k.key().0[12..32]);
            accounts_touched.insert(account_address);
        }
    }

    println!("Touched accounts:");
    for x in &accounts_touched {
        println!("  {:?}", x);
    }

    let state: rHashMap<B160, Account> = accounts_touched
        .iter()
        .map(|account| {
            let account_b160: B160 = h160_to_b160(*account);

            let storage: Option<rHashMap<revmU256, StorageSlot>> =
                account_to_keys.get(account).map(|slot_changes| {
                    slot_changes
                        .iter()
                        .map(|(slot, value)| {
                            (
                                h256_to_revm_u256(*slot.key()),
                                StorageSlot {
                                    original_value: revm::primitives::U256::ZERO, // FIXME
                                    present_value: h256_to_revm_u256(*value),
                                },
                            )
                        })
                        .collect()
                });
            let mut mm = bar.db.lock().unwrap();

            let account_code = fetch_account_code(
                account.clone(),
                &mut mm.as_mut(),
                &modified_keys,
                &bytecodes,
            );

            if let Some(account_code) = &account_code {
                println!(
                    "Setting accoutn code for {:?} hash: {:?} len {:?}",
                    account,
                    account_code.hash,
                    account_code.bytes().len()
                );
            }

            (
                account_b160,
                Account {
                    info: AccountInfo {
                        balance: revm::primitives::U256::ZERO, // FIXME
                        nonce: 1,                              // FIXME
                        code_hash: account_code
                            .as_ref()
                            .map(|x| x.hash().clone())
                            .unwrap_or_default(), // FIXME
                        code: account_code,
                    },
                    storage: storage.unwrap_or_default(),
                    storage_cleared: false,
                    is_destroyed: false,
                    is_touched: true,
                    is_not_existing: false,
                },
            )
        })
        .collect();

    Ok(ResultAndState {
        result: execution_result,
        state,
    })
}
