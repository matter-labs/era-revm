use std::{
    fmt::Debug,
    sync::{Arc, Mutex, RwLock},
};

use era_test_node::{
    fork::{ForkDetails, RemoteForkProvider},
    node::InMemoryNode,
    L2Tx, ShowCalls,
};
use revm::{
    primitives::{
        ruint::Uint, Account, AccountInfo, Bytes, EVMResult, Env, Eval, ExecutionResult, HashMap,
        ResultAndState, StorageSlot, TxEnv, B160, B256,
    },
    Database, Inspector,
};
use zksync_basic_types::{L1BatchNumber, L2ChainId, MiniblockNumber, H160, H256, U256};
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

pub struct RevmDatabaseForEra {
    pub db: Arc<Mutex<Box<dyn Database<Error = DatabaseError> + Send>>>,
}

impl Debug for RevmDatabaseForEra {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RevmDatabaseForEra")
            .field("db", &"db")
            .finish()
    }
}

impl RemoteForkProvider for RevmDatabaseForEra {
    fn get_storage_at(
        &self,
        address: H160,
        idx: U256,
        block: Option<BlockIdVariant>,
    ) -> Option<H256> {
        // Only top block is supported.
        assert!(block.is_none());
        let mut db = self.db.lock().unwrap();
        let result = db
            .storage(h160_to_b160(address), u256_to_revm_u256(idx))
            .unwrap();
        Some(revm_u256_to_h256(result))
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

pub fn tx_env_to_era_tx(tx_env: TxEnv) -> L2Tx {
    match tx_env.transact_to {
        revm::primitives::TransactTo::Call(contract_address) => L2Tx::new(
            contract_address.as_fixed_bytes().into(),
            tx_env.data.to_vec(),
            (tx_env.nonce.unwrap() as u32).into(),
            Fee {
                gas_limit: tx_env.gas_limit.into(),
                max_fee_per_gas: U256::from_little_endian(tx_env.gas_price.as_le_slice()),
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
        revm::primitives::TransactTo::Create(_) => todo!(),
    }
}

#[derive(Debug, Clone)]
pub enum DatabaseError {
    MissingCode(bool),
}

pub fn run_era_transaction(
    env: Env,
    db: &dyn Database<Error = DatabaseError>,
    inspector: &mut dyn Inspector<dyn Database<Error = DatabaseError>>,
) -> EVMResult<DatabaseError> {
    // TODO - pass chain_id from env.cfg_env
    // TODO: pass stuff from block env (block number etc) into fork.

    let foo = Arc::new(Mutex::new(Box::new(db)));

    let aa = env.block.number.to::<u64>();

    let fork_details = ForkDetails {
        fork: Box::new(RevmDatabaseForEra { db: foo }),
        l1_block: L1BatchNumber(env.block.number.to::<u32>()),
        l2_miniblock: env.block.number.to::<u64>(),
        block_timestamp: env.block.timestamp.to::<u64>(),
        overwrite_chain_id: Some(L2ChainId(env.cfg.chain_id.to::<u16>())),
        l1_gas_price: env.block.basefee.to::<u64>(),
    };

    let node = InMemoryNode::new(None, ShowCalls::None, false, false);

    let l2_tx = tx_env_to_era_tx(env.tx.clone());

    let era_execution_result = node.run_l2_tx_for_revm(l2_tx).unwrap();

    let (modified_keys, tx_result, block, bytecodes) = era_execution_result;

    let execution_result = match tx_result.status {
        zksync_types::tx::tx_execution_info::TxExecutionStatus::Success => {
            ExecutionResult::Success {
                reason: Eval::Return,
                gas_used: env.tx.gas_limit - tx_result.gas_refunded as u64,
                gas_refunded: tx_result.gas_refunded as u64,
                logs: vec![],
                output: revm::primitives::Output::Create(Bytes::new(), None),
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
