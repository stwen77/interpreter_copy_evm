pub trait Ext {
    /// Check if running in static context.
    fn is_static(&self) -> bool;
}
pub struct Externalities {
    depth: usize,
    stack_depth: usize,
    static_flag: bool,
}

impl Ext for Externalities {
    fn is_static(&self) -> bool {
        return self.static_flag;
    }
}
