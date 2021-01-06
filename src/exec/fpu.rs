//! Everything related to the floating-point unit (FPU).

use std::num::FpCategory;
use super::registers::{Status, Control, Tag, TagValue};
use crate::common::f80::{self, F80};

/// The complete FPU unit.
/// 
/// FPU value registers are not exposed on their own because they have interactions among one another
/// and other internal FPU state registers that would make the separation pointless.
pub struct FPU {
    /// The physical value registers.
    /// These are exposed so that they can be used in external calculations,
    /// however care should be taken when mutating them directly, as this would not take into account the other registers.
    pub vals: [F80; 8],
    pub control: Control,
    pub status: Status,
    pub tag: Tag,
}
impl FPU {
    /// Creates a new FPU in the initialized state.
    pub fn new() -> Self {
        FPU {
            vals: [f80::POSITIVE_ZERO; 8],
            control: Control(0x3bf),
            status: Status(0),
            tag: Tag(0xffff),
        }
    }
    /// Clears the fpu back to the initialized state.
    pub fn reset(&mut self) {
        self.control.0 = 0x3bf;
        self.status.0 = 0;
        self.tag.0 = 0xffff;
    }
    /// Clears the exception bits from the status register.
    pub fn clear_exceptions(&mut self) {
        self.status.0 &= 0x7f00;
    }

    /// Converts a stack-top (ST) relative index to a physical index.
    /// A physical index is needed to directly use the stored register values or get a specific value from the tag register.
    /// Note that this will change if the `top` field is changed in the status register.
    pub fn st_to_physical(&self, st: u8) -> u8 {
        assert!(st < 8);
        (st + self.status.get_top()) & 7
    }

    fn set_physical(&mut self, physical: u8, val: F80) {
        self.vals[physical as usize] = val;
        self.tag.set_physical(physical, match val.classify() {
            FpCategory::Infinite | FpCategory::Nan => TagValue::Special,
            FpCategory::Zero => TagValue::Zero,
            _ => TagValue::NonZero,
        });
    }
    /// Assigns a value to the specified ST register.
    /// Updates the tag register accordingly.
    pub fn set_st(&mut self, st: u8, val: F80) { self.set_physical(self.st_to_physical(st), val) }
    /// Gets the value in the specified ST register.
    /// If the tag for that register is marked Empty, returns None.
    pub fn get_st(&self, st: u8) -> Option<F80> {
        let physical = self.st_to_physical(st);
        if self.tag.get_physical(physical) != TagValue::Empty as u8 { Some(self.vals[physical as usize]) } else { None }
    }
    /// Frees the specified ST register.
    /// This sets its tag to empty, but does not modify the value register.
    pub fn free_st(&mut self, st: u8) { self.tag.set_physical(self.st_to_physical(st), TagValue::Empty) }

    /// Pushes a value onto the fpu stack.
    /// Updates the status and tag registers accordingly.
    /// Fails if the push location is non-empty, in which case this operation is no-op.
    pub fn push(&mut self, val: F80) -> Result<(), ()> {
        let physical = self.status.get_top().wrapping_sub(1) & 7;
        if self.tag.get_physical(physical) != TagValue::Empty as u8 {
            return Err(());
        }
        self.set_physical(physical, val); // this updates the tag
        self.status.assign_top(physical);
        Ok(())
    }
    /// Pops a value off the fpu stack.
    /// Updates the status and tag registers accordingly, but the (logically) removed value is not modified.
    /// Fails if the pop location is empty, in which case this operation is no-op.
    pub fn pop(&mut self) -> Result<(), ()> {
        let physical = self.status.get_top();
        if self.tag.get_physical(physical) == TagValue::Empty as u8 {
            return Err(());
        }
        self.tag.set_physical(physical, TagValue::Empty);
        self.status.assign_top((physical + 1) & 7);
        Ok(())
    }
}
impl Default for FPU {
    fn default() -> FPU {
        FPU::new()
    }
}