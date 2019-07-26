use super::call_type::CallType;
use super::return_data::ReturnData;
use super::schedule::*;
use ethereum_types::{Address, H256, U256};

#[derive(Debug)]
/// Result of externalities call function.
pub enum MessageCallResult {
    /// Returned when message call was successfull.
    /// Contains gas left and output data.
    Success(U256, ReturnData),
    /// Returned when message call failed.
    /// VM doesn't have to know the reason.
    Failed,
    /// Returned when message call was reverted.
    /// Contains gas left and output data.
    Reverted(U256, ReturnData),
}
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
    /// Message call.
    ///
    /// Returns Err, if we run out of gas.
    /// Otherwise returns call_result which contains gas left
    /// and true if subcall was successfull.
    fn call(
        &mut self,
        gas: &U256,
        sender_address: &Address,
        receive_address: &Address,
        value: Option<U256>,
        data: &[u8],
        code_address: &Address,
        call_type: CallType,
        trap: bool,
    ) -> ::std::result::Result<MessageCallResult, ()>;
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
    ) -> ::std::result::Result<ContractCreateResult, ()> {
        return Err(());
    }
    fn call(
        &mut self,
        gas: &U256,
        sender_address: &Address,
        receive_address: &Address,
        value: Option<U256>,
        data: &[u8],
        code_address: &Address,
        call_type: CallType,
        trap: bool,
    ) -> ::std::result::Result<MessageCallResult, ()> {
        return Err(());
    }
}
