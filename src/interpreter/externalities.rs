use super::return_data::ReturnData;
use super::schedule::*;
use ethereum_types::{Address, H256, U256};

/// Specifies how an address is calculated for a new contract.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum CreateContractAddress {
    /// Address is calculated from sender and nonce. pWASM `create` scheme.
    FromSenderAndNonce,
    /// Address is calculated from sender, salt and code hash. pWASM `create2` scheme and EIP-1014 CREATE2 scheme.
    FromSenderSaltAndCodeHash(H256),
    /// Address is calculated from code hash and sender. Used by pwasm create ext.
    FromSenderAndCodeHash,
}

#[derive(Debug)]
/// Result of externalities create function.
pub enum ContractCreateResult {
    /// Returned when creation was successfull.
    /// Contains an address of newly created contract and gas left.
    Created(Address, U256),
    /// Returned when contract creation failed.
    /// VM doesn't have to know the reason.
    Failed,
    /// Reverted with REVERT.
    Reverted(U256, ReturnData),
}

pub trait Ext {
    /// Check if running in static context.
    fn is_static(&self) -> bool;
    /// Returns address balance.
    fn balance(&self, address: &Address) -> Result<U256, ()>;
    /// Returns current depth of execution.
    ///
    /// If contract A calls contract B, and contract B calls C,
    /// then A depth is 0, B is 1, C is 2 and so on.
    fn depth(&self) -> usize;
    /// Returns schedule.
    fn schedule(&self) -> &Schedule;
    /// Creates new contract.
    ///
    /// Returns gas_left and contract address if contract creation was succesfull.
    fn create(
        &mut self,
        gas: &U256,
        value: &U256,
        code: &[u8],
        address: CreateContractAddress,
        trap: bool,
    ) -> Result<ContractCreateResult, ()>;
}
pub struct Externalities<'a> {
    depth: usize,
    stack_depth: usize,
    static_flag: bool,
    schedule: &'a Schedule,
}

impl Ext for Externalities<'_> {
    fn is_static(&self) -> bool {
        return self.static_flag;
    }
    fn balance(&self, address: &Address) -> Result<U256, ()> {
        return Ok(U256::from(0));
        //stub
    }
    fn depth(&self) -> usize {
        self.depth
    }
    fn schedule(&self) -> &Schedule {
        self.schedule
    }
    fn create(
        &mut self,
        gas: &U256,
        value: &U256,
        code: &[u8],
        address_scheme: CreateContractAddress,
        trap: bool,
    ) -> ::std::result::Result<ContractCreateResult, TrapKind> {
        // create new contract address
        let (address, code_hash) = match self.state.nonce(&self.origin_info.address) {
            Ok(nonce) => contract_address(address_scheme, &self.origin_info.address, &nonce, &code),
            Err(e) => {
                debug!(target: "ext", "Database corruption encountered: {:?}", e);
                return Ok(ContractCreateResult::Failed);
            }
        };

        // prepare the params
        let params = ActionParams {
            code_address: address.clone(),
            address: address.clone(),
            sender: self.origin_info.address.clone(),
            origin: self.origin_info.origin.clone(),
            gas: *gas,
            gas_price: self.origin_info.gas_price,
            value: ActionValue::Transfer(*value),
            code: Some(Arc::new(code.to_vec())),
            code_hash: code_hash,
            data: None,
            call_type: CallType::None,
            params_type: vm::ParamsType::Embedded,
        };

        if !self.static_flag {
            if !self.schedule.keep_unsigned_nonce || params.sender != UNSIGNED_SENDER {
                if let Err(e) = self.state.inc_nonce(&self.origin_info.address) {
                    debug!(target: "ext", "Database corruption encountered: {:?}", e);
                    return Ok(ContractCreateResult::Failed);
                }
            }
        }

        if trap {
            return Err(TrapKind::Create(params, address));
        }

        // TODO: handle internal error separately
        let mut ex = Executive::from_parent(
            self.state,
            self.env_info,
            self.machine,
            self.schedule,
            self.depth,
            self.static_flag,
        );
        let out = ex.create_with_crossbeam(
            params,
            self.substate,
            self.stack_depth + 1,
            self.tracer,
            self.vm_tracer,
        );
        Ok(into_contract_create_result(out, &address, self.substate))
    }
}
