use ethereum_types::{Address, H256, U256};
use return_data::ReturnData;

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
