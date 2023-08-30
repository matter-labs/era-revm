/// RevmDatabaseForEra allows era VM to use the revm "Database" object
/// as a read-only fork source.
/// This way, we can run transaction on top of the chain that is persisted
/// in the Database object.
/// This code doesn't do any mutatios to Database: after each transaction run, the Revm
/// is usually collecing all the diffs - and applies them to database itself.
use std::{
    fmt::Debug,
    str::FromStr,
    sync::{Arc, Mutex},
};

use crate::conversion_utils::h256_to_b256;
use era_test_node::fork::ForkSource;
use revm::Database;
use zksync_basic_types::{MiniblockNumber, H160, H256, U256};
use zksync_types::{
    api::{BlockIdVariant, Transaction},
    L2_ETH_TOKEN_ADDRESS, SYSTEM_CONTEXT_ADDRESS,
};

use zksync_utils::u256_to_h256;

use crate::conversion_utils::{h160_to_b160, revm_u256_to_h256, u256_to_revm_u256};
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

impl<DB: Database + Send> RevmDatabaseForEra<DB>
where
    <DB as revm::Database>::Error: Debug,
{
    /// Returns the current block number and timestamp from the database.
    /// Reads it directly from the SYSTEM_CONTEXT storage.
    pub fn block_number_and_timestamp(&self) -> (u64, u64) {
        let num_and_ts = self.read_storage_internal(SYSTEM_CONTEXT_ADDRESS, U256::from(7));
        let num_and_ts_bytes = num_and_ts.as_fixed_bytes();
        let num: [u8; 8] = num_and_ts_bytes[24..32].try_into().unwrap();
        let ts: [u8; 8] = num_and_ts_bytes[8..16].try_into().unwrap();

        (u64::from_be_bytes(num), u64::from_be_bytes(ts))
    }

    fn read_storage_internal(&self, address: H160, idx: U256) -> H256 {
        let mut db = self.db.lock().unwrap();
        let result = db
            .storage(h160_to_b160(address), u256_to_revm_u256(idx))
            .unwrap();
        revm_u256_to_h256(result)
    }
}

impl<DB: Database + Send> ForkSource for &RevmDatabaseForEra<DB>
where
    <DB as revm::Database>::Error: Debug,
{
    fn get_storage_at(
        &self,
        address: H160,
        idx: U256,
        block: Option<BlockIdVariant>,
    ) -> eyre::Result<H256> {
        // We cannot support historical lookups. Only the most recent block is supported.
        if let Some(block) = &block {
            match block {
                BlockIdVariant::BlockNumber(number) => match number {
                    zksync_types::api::BlockNumber::Number(num) => {
                        let (current_block_number, _) = self.block_number_and_timestamp();

                        if num.as_u64() != current_block_number {
                            eyre::bail!("Only fetching of the most recent block {} is supported - but queried for {}", current_block_number, num)
                        }
                    }
                    _ => eyre::bail!("Only fetching most recent block is implemented"),
                },
                _ => eyre::bail!("Only fetching most recent block is implemented"),
            }
        }
        println!("Reading storage at {:?} idx: {:?}", address, idx);
        let mut result = self.read_storage_internal(address, idx);

        if L2_ETH_TOKEN_ADDRESS == address && result.is_zero() {
            // TODO: here we should read the account information from the Database trait
            // and lookup how many token it holds.
            // Unfortunately the 'idx' here is a hash of the account and Database doesn't
            // support getting a list of active accounts.
            // So for now - simply assume that every user has infinite money.
            result = u256_to_h256(U256::from(9_223_372_036_854_775_808 as u64));
        }
        Ok(result)
    }

    fn get_raw_block_transactions(
        &self,
        _block_number: MiniblockNumber,
    ) -> eyre::Result<Vec<zksync_types::Transaction>> {
        todo!()
    }

    fn get_bytecode_by_hash(&self, hash: H256) -> eyre::Result<Option<Vec<u8>>> {
        let mut db = self.db.lock().unwrap();
        let result = db.code_by_hash(h256_to_b256(hash)).unwrap();
        Ok(Some(result.bytecode.to_vec()))
    }

    fn get_transaction_by_hash(&self, _hash: H256) -> eyre::Result<Option<Transaction>> {
        todo!()
    }
}
