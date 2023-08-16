use std::{
    fmt::Debug,
    str::FromStr,
    sync::{Arc, Mutex, RwLock},
};

use era_test_node::{
    fork::{ForkDetails, RemoteForkProvider},
    node::{contract_address_from_tx_result, InMemoryNode},
    L2Tx, ShowCalls,
};
use revm::{
    primitives::{
        ruint::Uint, Account, AccountInfo, Bytes, EVMResult, Env, Eval, ExecutionResult, HashMap,
        ResultAndState, StorageSlot, TxEnv, B160, B256,
    },
    Database, Inspector,
};
use zksync_basic_types::{
    web3::signing::keccak256, L1BatchNumber, L2ChainId, MiniblockNumber, H160, H256, U256,
};
use zksync_types::{
    api::{BlockIdVariant, Transaction},
    fee::Fee,
    transaction_request::PaymasterParams,
    StorageKey,
};

use revm::primitives::U256 as revmU256;

fn b160_to_h160(i: B160) -> H160 {
    i.as_fixed_bytes().into()
}

fn h160_to_b160(i: H160) -> B160 {
    i.as_fixed_bytes().into()
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_160_conversion() {
        let b = B160::from_str("0x000000000000000000000000000000000000800b").unwrap();
        let h = b160_to_h160(b);
        assert_eq!(h.to_string(), "0x0000…800b");
        let b2 = h160_to_b160(h);
        assert_eq!(b, b2);
    }

    #[test]
    fn test_256_conversion() {
        let h =
            H256::from_str("0xb99acb716b354b9be88d3eaba99ad36792ccdd4349404cbb812adf0b0b14d601")
                .unwrap();
        let b = h256_to_b256(h);
        assert_eq!(b.to_string(), "0xb99a…d601");
        let u = h256_to_u256(h);
        assert_eq!(
            u.to_string(),
            "83951375548152864551218308881540843734370423742152710934930688330188941743617"
        );

        let revm_u = u256_to_revm_u256(u);
        assert_eq!(
            revm_u.to_string(),
            "83951375548152864551218308881540843734370423742152710934930688330188941743617"
        );
        assert_eq!(u, revm_u256_to_u256(revm_u));

        assert_eq!(h, revm_u256_to_h256(revm_u));

        assert_eq!(h, u256_to_h256(u));
    }
}

fn u256_to_b256(i: U256) -> B256 {
    let mut payload: [u8; 32] = [0; 32];
    i.to_big_endian(&mut payload);
    B256::from_slice(&payload)
}

fn u256_to_revm_u256(i: U256) -> revmU256 {
    let mut payload: [u8; 32] = [0; 32];
    i.to_big_endian(&mut payload);
    revmU256::from_be_bytes(payload)
}

fn revm_u256_to_u256(i: revmU256) -> U256 {
    U256::from_big_endian(&i.to_be_bytes::<32>())
}

fn revm_u256_to_h256(i: revmU256) -> H256 {
    i.to_be_bytes::<32>().into()
}

fn h256_to_b256(i: H256) -> B256 {
    i.to_fixed_bytes().into()
}

fn h256_to_u256(i: H256) -> U256 {
    i.to_fixed_bytes().into()
}
fn u256_to_h256(i: U256) -> H256 {
    let mut bytes = [0u8; 32];
    i.to_big_endian(&mut bytes);
    H256::from_slice(&bytes)
}

pub struct RevmDatabaseForEra<DB> {
    pub db: Arc<Mutex<Box<DB>>>,
}

impl<DB> Debug for RevmDatabaseForEra<DB> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RevmDatabaseForEra")
            .field("db", &"db")
            .finish()
    }
}

impl<DB: Database + Send> RemoteForkProvider for RevmDatabaseForEra<DB>
where
    <DB as revm::Database>::Error: Debug,
{
    fn get_storage_at(
        &self,
        address: H160,
        idx: U256,
        block: Option<BlockIdVariant>,
    ) -> Option<H256> {
        let l2_token = H160::from_str("0x000000000000000000000000000000000000800a").unwrap();
        // Only top block is supported.
        // FIXME
        //assert!(block.is_none());
        println!("Reading storage at {:?} idx: {:?}", address, idx);
        let mut db = self.db.lock().unwrap();
        let result = db
            .storage(h160_to_b160(address), u256_to_revm_u256(idx))
            .unwrap();
        let mut result = revm_u256_to_h256(result);

        if l2_token == address && result.is_zero() {
            result = u256_to_h256(U256::from(9_223_372_036_854_775_808 as u64));
            println!("Faking L2 token");
        }
        println!("Got result: {:?}", result);
        Some(result)
    }

    fn get_raw_block_transactions(
        &self,
        block_number: MiniblockNumber,
    ) -> Option<Vec<zksync_types::Transaction>> {
        todo!()
    }

    fn get_bytecode_by_hash(&self, hash: H256) -> Option<Vec<u8>> {
        let mut db = self.db.lock().unwrap();
        let result = db.code_by_hash(h256_to_b256(hash)).unwrap();
        Some(result.bytecode.to_vec())
    }

    fn get_transaction_by_hash(&self, hash: H256) -> Option<Transaction> {
        todo!()
    }
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

pub fn tx_env_to_era_tx(tx_env: TxEnv) -> L2Tx {
    println!(
        "Creating transaction with nonce: {:?} from: {:?}",
        tx_env.nonce, tx_env.caller
    );
    let mut l2tx = match tx_env.transact_to {
        revm::primitives::TransactTo::Call(contract_address) => L2Tx::new(
            contract_address.as_fixed_bytes().into(),
            tx_env.data.to_vec(),
            (tx_env.nonce.unwrap_or_default() as u32).into(),
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
            let bytecode = tx_env.data.to_vec();
            let bytecode_hash = hash_bytecode(&bytecode);
            L2Tx::new(
                H160::from_low_u64_be(0x8006),
                // TODO: wrap tx_env.data !!
                encode_deploy_params_create(Default::default(), bytecode_hash, Default::default()),
                //tx_env.data.to_vec(),
                (tx_env.nonce.unwrap_or_default() as u32).into(),
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
                Some(vec![bytecode]), // factory_deps
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

pub fn run_era_transaction<'a, DB, E, INSP>(
    env: &Env,
    db: DB,
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
    let bar = RevmDatabaseForEra { db: foo };

    let fork_details = ForkDetails {
        fork: &bar,
        l1_block: L1BatchNumber(env.block.number.to::<u32>() - 1), // HACK
        l2_miniblock: env.block.number.to::<u64>() - 1,
        block_timestamp: env.block.timestamp.to::<u64>(),
        overwrite_chain_id: Some(L2ChainId(env.cfg.chain_id.to::<u16>())),
        l1_gas_price: set_min_l1_gas_price(env.block.basefee.to::<u64>()),
    };

    let node = InMemoryNode::new(Some(fork_details), ShowCalls::All, false, false);

    // TODO: get nonce on your own (from the database).
    let l2_tx = tx_env_to_era_tx(env.tx.clone());

    let era_execution_result = node.run_l2_tx_for_revm(l2_tx).unwrap();

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
        zksync_types::tx::tx_execution_info::TxExecutionStatus::Failure => todo!(),
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

    let state = account_to_keys
        .iter()
        .map(|(address, slot_changes)| {
            let storage = slot_changes
                .iter()
                .map(|(slot, value)| {
                    (
                        revm::primitives::U256::from_le_bytes(slot.key().0),
                        StorageSlot {
                            original_value: revm::primitives::U256::ZERO, // FIXME
                            present_value: revm::primitives::U256::from_le_bytes(
                                value.to_fixed_bytes(),
                                // TODO: verify endianness
                            ),
                        },
                    )
                })
                .collect();
            (
                B160::from(address.0),
                Account {
                    info: AccountInfo {
                        balance: revm::primitives::U256::ZERO, // FIXME
                        nonce: 1,                              // FIXME
                        code_hash: B256::zero(),               // FIXME
                        code: None,
                    },
                    storage,
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
/*
pub fn foobar() {
    match revm::evm_inner::<Self, true>(env, self, &mut inspector).transact() {
        Ok(res) => Ok(res),
        Err(e) => eyre::bail!("backend: failed while inspecting: {:?}", e),
    }
}*/
