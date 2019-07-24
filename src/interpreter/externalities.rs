use super::schedule::*;
use ethereum_types::{Address, H256, U256};

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
}
pub struct Externalities<'a> {
    depth: usize,
    stack_depth: usize,
    static_flag: bool,
    schedule: &'a Schedule,
}

impl Ext for Externalities {
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
}
