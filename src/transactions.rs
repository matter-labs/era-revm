use std::{
    collections::{HashMap, HashSet},
    fmt::Debug,
    sync::{Arc, Mutex},
};
use multivm::interface::VmExecutionResultAndLogs;
use era_test_node::{fork::ForkDetails, node::InMemoryNode, system_contracts};
use revm::{
    primitives::{
        Account, AccountInfo, Bytes, EVMResult, Env, Eval, ExecutionResult, HashMap as rHashMap,
        ResultAndState, StorageSlot, TxEnv, B160,
    },
    Database,
};
use zksync_basic_types::{web3::signing::keccak256, L1BatchNumber, H160, H256, U256};
use zksync_types::{
    fee::Fee, l2::L2Tx, transaction_request::PaymasterParams, StorageKey, StorageLogQueryType,
    L2ChainId,
    ACCOUNT_CODE_STORAGE_ADDRESS,
};

use revm::primitives::U256 as revmU256;
use zksync_utils::{h256_to_account_address, u256_to_h256};

use crate::{
    conversion_utils::{
        b160_to_h160, h160_to_b160, h256_to_h160, h256_to_revm_u256, revm_u256_to_u256,
        u256_to_revm_u256,
    },
    db::RevmDatabaseForEra,
    factory_deps::PackedEraBytecode,
};

fn contract_address_from_tx_result(execution_result: &VmExecutionResultAndLogs) -> Option<H160> {
    for query in execution_result.logs.storage_logs.iter().rev() {
        if query.log_type == StorageLogQueryType::InitialWrite
            && query.log_query.address == ACCOUNT_CODE_STORAGE_ADDRESS
        {
            return Some(h256_to_account_address(&u256_to_h256(query.log_query.key)));
        }
    }
    None
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

/// Extract the zkSync Fee based off the Revm transaction.
pub fn tx_env_to_fee(tx_env: &TxEnv) -> Fee {
    Fee {
        // Currently zkSync doesn't allow gas limits larger than u32.
        gas_limit: U256::min(tx_env.gas_limit.into(), U256::from(2147483640)),
        // Block base fee on L2 is 0.25 GWei - make sure that the max_fee_per_gas is set to higher value.
        max_fee_per_gas: U256::max(revm_u256_to_u256(tx_env.gas_price), U256::from(260_000_000)),
        max_priority_fee_per_gas: revm_u256_to_u256(tx_env.gas_priority_fee.unwrap_or_default()),
        gas_per_pubdata_limit: U256::from(800),
    }
}

/// Translates Revm transaction into era's L2Tx.
pub fn tx_env_to_era_tx(tx_env: TxEnv, nonce: u64) -> L2Tx {
    let mut l2tx = match tx_env.transact_to {
        revm::primitives::TransactTo::Call(contract_address) => L2Tx::new(
            contract_address.as_fixed_bytes().into(),
            tx_env.data.to_vec(),
            (tx_env.nonce.unwrap_or(nonce) as u32).into(),
            tx_env_to_fee(&tx_env),
            tx_env.caller.as_fixed_bytes().into(),
            revm_u256_to_u256(tx_env.value),
            None, // factory_deps
            PaymasterParams::default(),
        ),
        revm::primitives::TransactTo::Create(_scheme) => {
            // TODO: support create / create2.
            let packed_bytecode = PackedEraBytecode::from_vec(&tx_env.data.to_vec());
            L2Tx::new(
                H160::from_low_u64_be(0x8006),
                encode_deploy_params_create(
                    Default::default(),
                    packed_bytecode.bytecode_hash(),
                    Default::default(),
                ),
                (tx_env.nonce.unwrap_or(nonce) as u32).into(),
                tx_env_to_fee(&tx_env),
                tx_env.caller.as_fixed_bytes().into(),
                revm_u256_to_u256(tx_env.value),
                Some(packed_bytecode.factory_deps()),
                PaymasterParams::default(),
            )
        }
    };
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

pub fn run_era_transaction<'a, DB, E, INSP>(
    env: &mut Env,
    db: &mut DB,
    _inspector: INSP,
) -> EVMResult<E>
where
    DB: Database + Send + 'a,
    <DB as revm::Database>::Error: Debug,
{
    let era_db = RevmDatabaseForEra {
        db: Arc::new(Mutex::new(Box::new(db))),
    };

    let (num, ts) = era_db.block_number_and_timestamp();

    let nonces = era_db.get_nonce_for_address(b160_to_h160(env.tx.caller));

    println!(
        "*** Starting ERA transaction: block: {:?} timestamp: {:?} - but using {:?} and {:?} instead with nonce {:?}",
        env.block.number.to::<u32>(),
        env.block.timestamp.to::<u64>(),
        num,
        ts,
        nonces
    );

    // Update the environment timestamp and block number.
    // Check if this should be done at the end?
    env.block.number = u256_to_revm_u256(U256::from(num));
    env.block.timestamp = u256_to_revm_u256(U256::from(ts));

    let fork_details = ForkDetails {
        fork_source: &era_db,
        l1_block: L1BatchNumber(num as u32),
        l2_block: num,
        l2_miniblock: num,
        l2_miniblock_hash: Default::default(),
        block_timestamp: ts,
        overwrite_chain_id: Some(L2ChainId(env.cfg.chain_id.to::<u16>())),
        // Make sure that l1 gas price is set to reasonable values.
        l1_gas_price: u64::max(env.block.basefee.to::<u64>(), 1000),
    };

    let node = InMemoryNode::new(
        Some(fork_details),
        None,
        Default::default(),
        // era_test_node::node::ShowCalls::None,
        // InMemoryNodeConfig::default(),
        // era_test_node::node::ShowStorageLogs::None,
        // era_test_node::node::ShowVMDetails::None,
        // era_test_node::node::ShowGasDetails::None,
        // false,
        // // Disable security on default accounts.
        // &system_contracts::Options::BuiltInWithoutSecurity,
    );

    let l2_tx = tx_env_to_era_tx(env.tx.clone(), nonces);

    let era_execution_result = node
        .run_l2_tx_inner(
            l2_tx,
            multivm::interface::TxExecutionMode::VerifyExecute,
        )
        .unwrap();

    let (modified_keys, tx_result, _block, bytecodes, _, _) = era_execution_result;
    let maybe_contract_address = contract_address_from_tx_result(&tx_result);

    let execution_result = match tx_result.result {
        ExecutionResult::Success { output, .. } => {
            ExecutionResult::Success {
                reason: Eval::Return,
                gas_used: env.tx.gas_limit - tx_result.refunds.gas_refunded as u64,
                gas_refunded: tx_result.refunds.gas_refunded as u64,
                logs: vec![],
                output: revm::primitives::Output::Create(
                    Bytes::new(), // FIXME (function results)
                    maybe_contract_address.map(|address| h160_to_b160(address)),
                ),
            }
        }
        ExecutionResult::Revert { .. } | ExecutionResult::Halt { .. } => {
            ExecutionResult::Revert {
                gas_used: env.tx.gas_limit - tx_result.refunds.gas_refunded as u64,
                output: Bytes::new(), // FIXME (function results)
            }
        }
    };
    

    let account_to_keys: HashMap<H160, HashMap<StorageKey, H256>> =
        modified_keys
            .iter()
            .fold(HashMap::new(), |mut acc, (storage_key, value)| {
                acc.entry(*storage_key.address())
                    .or_insert_with(HashMap::new)
                    .insert(*storage_key, *value);
                acc
            });

    // List of touched accounts
    let mut accounts_touched: HashSet<H160> = Default::default();
    // All accounts where storage was modified.
    for x in account_to_keys.keys() {
        accounts_touched.insert(x.clone());
    }
    // Also insert 'fake' accounts for bytecodes (to make sure that factory bytecodes get persisted).
    for (k, _) in &bytecodes {
        accounts_touched.insert(h256_to_h160(&u256_to_h256(*k)));
    }

    let account_code_storage = ACCOUNT_CODE_STORAGE_ADDRESS;

    if let Some(account_bytecodes) = account_to_keys.get(&account_code_storage) {
        for (k, _) in account_bytecodes {
            let account_address = H160::from_slice(&k.key().0[12..32]);
            accounts_touched.insert(account_address);
        }
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

            let account_code =
                era_db.fetch_account_code(account.clone(), &modified_keys, &bytecodes);

            (
                account_b160,
                Account {
                    info: AccountInfo {
                        balance: revm::primitives::U256::ZERO, // FIXME
                        nonce: era_db.get_nonce_for_address(*account),
                        code_hash: account_code
                            .as_ref()
                            .map(|x| x.hash().clone())
                            .unwrap_or_default(),
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
