use era_test_node::fork::{ForkSource, ForkStorage};
use era_test_node::utils::bytecode_to_factory_dep;
use ethers::{abi::AbiDecode, prelude::abigen};
use multivm::interface::dyn_tracers::vm_1_3_3::DynTracer;
use multivm::interface::tracer::TracerExecutionStatus;
use multivm::vm_refunds_enhancement::{
    BootloaderState, HistoryMode, SimpleMemory, VmTracer, ZkSyncVmState,
};
use multivm::zk_evm_1_3_3::tracing::{BeforeExecutionData, VmLocalStateData};
use std::fmt::Debug;
use zk_evm::zkevm_opcode_defs::{FatPointer, Opcode, CALL_IMPLICIT_CALLDATA_FAT_PTR_REGISTER};
use zksync_basic_types::{AccountTreeId, H160};
use zksync_state::{ReadStorage, StoragePtr, StorageView, WriteStorage};
use zksync_types::{
    block::{pack_block_info, unpack_block_info},
    get_code_key, get_nonce_key,
    utils::{decompose_full_nonce, nonces_to_full_nonce, storage_key_for_eth_balance},
    StorageKey,
};
use zksync_utils::{h256_to_u256, u256_to_h256};

// address(uint160(uint256(keccak256('hevm cheat code'))))
const CHEATCODE_ADDRESS: H160 = H160([
    113, 9, 112, 158, 207, 169, 26, 128, 98, 111, 243, 152, 157, 104, 246, 127, 91, 29, 209, 45,
]);

type ForkStorageView<S> = StorageView<ForkStorage<S>>;

abigen!(
    CheatcodeContract,
    r#"[
        function deal(address who, uint256 newBalance)
        function etch(address who, bytes calldata code)
        function setNonce(address account, uint64 nonce)
        function roll(uint256 blockNumber)
        function warp(uint256 timestamp)
    ]"#
);

#[derive(Debug, Clone)]
enum FinishCycleActions {}

#[derive(Clone, Debug, Default)]
pub struct CheatcodeTracer {
    actions: Vec<FinishCycleActions>,
}

impl<S: std::fmt::Debug + ForkSource, H: HistoryMode> DynTracer<ForkStorageView<S>, SimpleMemory<H>>
    for CheatcodeTracer
{
    fn before_execution(
        &mut self,
        state: VmLocalStateData<'_>,
        data: BeforeExecutionData,
        memory: &SimpleMemory<H>,
        storage: StoragePtr<ForkStorageView<S>>,
    ) {
        if let Opcode::NearCall(_call) = data.opcode.variant.opcode {
            let current = state.vm_local_state.callstack.current;
            if current.this_address != CHEATCODE_ADDRESS {
                return;
            }
            if current.code_page.0 == 0 || current.ergs_remaining == 0 {
                tracing::error!("cheatcode triggered, but no calldata or ergs available");
                return;
            }
            tracing::info!("near call: cheatcode triggered");
            let calldata = {
                let ptr = state.vm_local_state.registers
                    [CALL_IMPLICIT_CALLDATA_FAT_PTR_REGISTER as usize];
                assert!(ptr.is_pointer);
                let fat_data_pointer = FatPointer::from_u256(ptr.value);
                memory.read_unaligned_bytes(
                    fat_data_pointer.memory_page as usize,
                    fat_data_pointer.start as usize,
                    fat_data_pointer.length as usize,
                )
            };

            // try to dispatch the cheatcode
            if let Ok(call) = CheatcodeContractCalls::decode(calldata.clone()) {
                self.dispatch_cheatcode(state, data, memory, storage, call)
            } else {
                tracing::error!(
                    "Failed to decode cheatcode calldata (near call): {}",
                    hex::encode(calldata),
                );
            }
        }
    }
}

impl<S: std::fmt::Debug + ForkSource, H: HistoryMode> VmTracer<ForkStorageView<S>, H>
    for CheatcodeTracer
{
    fn finish_cycle(
        &mut self,
        _state: &mut ZkSyncVmState<ForkStorageView<S>, H>,
        _bootloader_state: &mut BootloaderState,
    ) -> TracerExecutionStatus {
        while let Some(_action) = self.actions.pop() {}
        TracerExecutionStatus::Continue
    }
}

impl CheatcodeTracer {
    pub fn new() -> Self {
        CheatcodeTracer { actions: vec![] }
    }

    pub fn dispatch_cheatcode<S: std::fmt::Debug + ForkSource, H: HistoryMode>(
        &mut self,
        _state: VmLocalStateData<'_>,
        _data: BeforeExecutionData,
        _memory: &SimpleMemory<H>,
        storage: StoragePtr<ForkStorageView<S>>,
        call: CheatcodeContractCalls,
    ) {
        use CheatcodeContractCalls::*;
        match call {
            Deal(DealCall { who, new_balance }) => {
                tracing::info!("Setting balance for {who:?} to {new_balance}");
                storage
                    .borrow_mut()
                    .set_value(storage_key_for_eth_balance(&who), u256_to_h256(new_balance));
            }
            Etch(EtchCall { who, code }) => {
                tracing::info!("Setting address code for {who:?}");
                let code_key = get_code_key(&who);
                let (hash, _code) = bytecode_to_factory_dep(code.0.into());
                let hash = u256_to_h256(hash);

                // TODO: store factory dep
                // self.revm_db.store_factory_dep(
                //     hash,
                //     code.iter()
                //         .flat_map(|entry| {
                //             let mut bytes = vec![0u8; 32];
                //             entry.to_big_endian(&mut bytes);
                //             bytes.to_vec()
                //         })
                //         .collect(),
                // );
                storage.borrow_mut().set_value(code_key, hash);
            }
            SetNonce(SetNonceCall { account, nonce }) => {
                tracing::info!("Setting nonce for {account:?} to {nonce}");
                let mut storage = storage.borrow_mut();
                let nonce_key = get_nonce_key(&account);
                let full_nonce = storage.read_value(&nonce_key);
                let (mut account_nonce, mut deployment_nonce) =
                    decompose_full_nonce(h256_to_u256(full_nonce));
                if account_nonce.as_u64() >= nonce {
                    tracing::error!(
                      "SetNonce cheatcode failed: Account nonce is already set to a higher value ({}, requested {})",
                      account_nonce,
                      nonce
                  );
                    return;
                }
                account_nonce = nonce.into();
                if deployment_nonce.as_u64() >= nonce {
                    tracing::error!(
                      "SetNonce cheatcode failed: Deployment nonce is already set to a higher value ({}, requested {})",
                      deployment_nonce,
                      nonce
                  );
                    return;
                }
                deployment_nonce = nonce.into();
                let enforced_full_nonce = nonces_to_full_nonce(account_nonce, deployment_nonce);
                tracing::info!(
                    "👷 Nonces for account {:?} have been set to {}",
                    account,
                    nonce
                );
                storage.set_value(nonce_key, u256_to_h256(enforced_full_nonce));
            }
            Roll(RollCall { block_number }) => {
                tracing::info!("Setting block number to {}", block_number);

                let key = StorageKey::new(
                    AccountTreeId::new(zksync_types::SYSTEM_CONTEXT_ADDRESS),
                    zksync_types::CURRENT_VIRTUAL_BLOCK_INFO_POSITION,
                );
                let mut storage = storage.borrow_mut();
                let (_, block_timestamp) =
                    unpack_block_info(h256_to_u256(storage.read_value(&key)));
                storage.set_value(
                    key,
                    u256_to_h256(pack_block_info(block_number.as_u64(), block_timestamp)),
                );
            }
            Warp(WarpCall { timestamp }) => {
                tracing::info!("Setting block timestamp {}", timestamp);

                let key = StorageKey::new(
                    AccountTreeId::new(zksync_types::SYSTEM_CONTEXT_ADDRESS),
                    zksync_types::CURRENT_VIRTUAL_BLOCK_INFO_POSITION,
                );
                let mut storage = storage.borrow_mut();
                let (block_number, _) = unpack_block_info(h256_to_u256(storage.read_value(&key)));
                storage.set_value(
                    key,
                    u256_to_h256(pack_block_info(block_number, timestamp.as_u64())),
                );
            }
        };
    }
}
