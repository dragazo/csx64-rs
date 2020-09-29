//! Everything related to the floating-point unit (FPU).

use std::num::FpCategory;
use rug::{Float, Assign};
use rug::float::Constant;
use super::registers::{Status, Control, Tag, TagValue};
use crate::common::util;

#[cfg(test)]
use rug::float::SmallFloat;

/// Number of precision bits for FPU calculations.
pub const MAX_PRECISION: u32 = 64; // IEEE-754 extended fp (f80) has 64 prec bits

lazy_static! {
    pub static ref PI: Float = Float::with_val(MAX_PRECISION, Constant::Pi);
    pub static ref E: Float = Float::with_val(MAX_PRECISION, 1).exp(); // no idea why this isn't a constant, but whatever

    pub static ref LOG2_10: Float = Float::with_val(MAX_PRECISION, 10).log2();
    pub static ref LOG2_E: Float = Float::with_val(MAX_PRECISION, &*E).log2();
    pub static ref LOG10_2: Float = Float::with_val(MAX_PRECISION, 2).log10();
    pub static ref LN_2: Float = Float::with_val(MAX_PRECISION, 2).ln();
}

/// The source of an FPU value: built-in or extended.
pub enum Source<'a> {
    /// Sources the value from some extended `Float` type.
    /// This can also be used for primitives like `f64` or `u64` via `rug::float::SmallFloat`, which implements deref to `Float`.
    Value(&'a Float),
    /// Sources the value from the FPU value register with the specified physical index.
    /// This is needed to efficiently copy values, because `Value` would borrow the `FPU`.
    /// Note that this will fail if the source register is currently empty.
    PhysicalRegister(u8),
}

/// The complete FPU unit.
/// 
/// FPU value registers are not exposed on their own because they have interactions among one another
/// and other internal FPU state registers that would make the separation pointless.
pub struct FPU {
    /// The physical value registers.
    /// These are exposed so that they can be used in external calculations,
    /// however care should be taken when mutating them directly, as this would not take into account the other registers.
    pub vals: [Float; 8],
    pub control: Control,
    pub status: Status,
    pub tag: Tag,
}
impl FPU {
    /// Computes the tag that would be given to the value.
    /// Note that this assumes the value has already been adjusted for correct precision and rounding.
    pub fn get_tag(val: &Float) -> TagValue {
        match val.classify() {
            FpCategory::Infinite | FpCategory::Nan => TagValue::Special,
            FpCategory::Zero => TagValue::Zero,
            _ => TagValue::NonZero,
        }
    }

    /// Creates a new FPU in the initialized state.
    pub fn new() -> Self {
        macro_rules! f { () => { Float::new(MAX_PRECISION) } }
        FPU {
            vals: [f!(), f!(), f!(), f!(), f!(), f!(), f!(), f!()],
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

    /// Converts a logical index (st index) to a physical index.
    /// Note that this will change if the `top` field is changed in the status register.
    pub fn st_to_physical(&self, st: u8) -> u8 {
        assert!(st < 8);
        (st + self.status.get_top()) & 7
    }

    /// Assigns a value to the specified physical register.
    /// Updates the tag register accordingly.
    /// This can assign to any target register, empty or not; the only way it can fail is if the source is an empty register.
    pub fn assign_physical(&mut self, index: u8, src: Source) -> Result<(), ()> {
        match src {
            Source::Value(v) => self.vals[index as usize].assign(v),
            Source::PhysicalRegister(v) => {
                if self.tag.get_physical(v) == TagValue::Empty as u8 { return Err(()); } // copying from empty is an error
                if v == index { return Ok(()); } // assigning to same register is no-op
                let (dest, src) = util::mut2(&mut self.vals, index as usize, v as usize);
                dest.assign(&*src);
            }
        }
        self.tag.set_physical(index, Self::get_tag(&self.vals[index as usize]));
        Ok(())
    }
    /// Frees the specified physical register.
    /// This sets its tag to empty, but does not modify the value register.
    pub fn free_physical(&mut self, index: u8) {
        self.tag.set_physical(index, TagValue::Empty);
    }

    /// Pushes a value onto the fpu stack.
    /// Updates the status and tag registers accordingly.
    /// Returns the physical index of the added value.
    /// Fails if the push location is non-empty, in which case this operation is no-op.
    pub fn push(&mut self, src: Source) -> Result<u8, ()> {
        let i = self.status.get_top().wrapping_sub(1) & 7;
        if self.tag.get_physical(i) != TagValue::Empty as u8 {
            return Err(());
        }
        self.assign_physical(i, src)?;
        self.status.set_top(i);
        Ok(i)
    }
    /// Pops a value off the fpu stack.
    /// Updates the status and tag registers accordingly, but the (logically) removed value is not modified.
    /// Returns the physical index of the removed value.
    /// Fails if the pop location is empty, in which case this operation is no-op.
    pub fn pop(&mut self) -> Result<u8, ()> {
        let i = self.status.get_top();
        if self.tag.get_physical(i) == TagValue::Empty as u8 {
            return Err(());
        }
        self.tag.set_physical(i, TagValue::Empty);
        self.status.set_top((i + 1) & 7);
        Ok(i)
    }
}

#[test]
fn test_fpu() {
    let mut fpu = FPU::new();
    assert_eq!(fpu.status.get_top(), 0);
    assert_eq!(fpu.st_to_physical(0), 0);
    assert_eq!(fpu.st_to_physical(4), 4);
    assert_eq!(fpu.st_to_physical(7), 7);

    let i = fpu.push(Source::Value(&*SmallFloat::from(3.78))).unwrap();
    assert_eq!(fpu.vals[i as usize].prec(), MAX_PRECISION);
    assert_eq!(fpu.tag.get_physical(i), TagValue::NonZero as u8);
    assert_eq!(fpu.status.get_top(), 7);
    assert_eq!(fpu.st_to_physical(0), 7);
    assert_eq!(fpu.st_to_physical(4), 3);
    assert_eq!(fpu.st_to_physical(7), 6);

    let j = fpu.push(Source::Value(&Float::with_val(MAX_PRECISION * 2, &*E))).unwrap();
    assert_eq!(fpu.vals[j as usize].prec(), MAX_PRECISION);
    assert_eq!(fpu.tag.get_physical(j), TagValue::NonZero as u8);
    assert_eq!(fpu.status.get_top(), 6);
    assert_eq!(fpu.st_to_physical(0), 6);
    assert_eq!(fpu.st_to_physical(4), 2);
    assert_eq!(fpu.st_to_physical(7), 5);

    let k = fpu.push(Source::Value(&Float::with_val(MAX_PRECISION / 2, Constant::Pi))).unwrap();
    assert_eq!(fpu.vals[k as usize].prec(), MAX_PRECISION);
    assert_eq!(fpu.tag.get_physical(k), TagValue::NonZero as u8);
    assert_eq!(fpu.status.get_top(), 5);
    assert_eq!(fpu.st_to_physical(0), 5);
    assert_eq!(fpu.st_to_physical(4), 1);
    assert_eq!(fpu.st_to_physical(7), 4);

    assert_eq!(i, 7);
    assert_eq!(j, 6);
    assert_eq!(k, 5);
    assert!((fpu.vals[i as usize].to_f64() - 3.78).abs() <= 0.00000000001);
    assert!((fpu.vals[j as usize].to_f64() - 2.718281828459045235360).abs() <= 0.00000000001);
    assert!((fpu.vals[k as usize].to_f64() - 3.1415926).abs() <= 0.000001);

    {
        let x = fpu.push(Source::Value(&*SmallFloat::from(f64::INFINITY))).unwrap();
        assert_eq!(fpu.tag.get_physical(x), TagValue::Special as u8);
        let val = &fpu.vals[x as usize];
        assert!(val.is_sign_positive() && val.is_infinite());
        assert_eq!(fpu.pop().unwrap(), x);
    }
    {
        let x = fpu.push(Source::Value(&*SmallFloat::from(f64::NEG_INFINITY))).unwrap();
        assert_eq!(fpu.tag.get_physical(x), TagValue::Special as u8);
        let val = &fpu.vals[x as usize];
        assert!(val.is_sign_negative() && val.is_infinite());
        assert_eq!(fpu.pop().unwrap(), x);
    }
    {
        let x = fpu.push(Source::Value(&*SmallFloat::from(f64::NAN))).unwrap();
        assert_eq!(fpu.tag.get_physical(x), TagValue::Special as u8);
        let val = &fpu.vals[x as usize];
        assert!(val.is_nan());
        assert_eq!(fpu.pop().unwrap(), x);
    }

    assert_eq!(fpu.status.get_top(), k);
    fpu.free_physical(i);
    assert_eq!(fpu.tag.get_physical(i), TagValue::Empty as u8);
    fpu.free_physical(k);
    assert_eq!(fpu.tag.get_physical(k), TagValue::Empty as u8);
    assert!((fpu.vals[i as usize].to_f64() - 3.78).abs() <= 0.00000000001);
    assert!((fpu.vals[j as usize].to_f64() - 2.718281828459045235360).abs() <= 0.00000000001);
    assert!((fpu.vals[k as usize].to_f64() - 3.1415926).abs() <= 0.000001);

    assert_eq!(fpu.status.get_top(), k);
    let prev = (fpu.status.0, fpu.tag.0, fpu.control.0);
    fpu.pop().unwrap_err();
    assert_eq!(prev, (fpu.status.0, fpu.tag.0, fpu.control.0));
    assert!((fpu.vals[k as usize].to_f64() - 3.1415926).abs() <= 0.000001);

    fpu.assign_physical(i, Source::PhysicalRegister(i)).unwrap_err();
    fpu.assign_physical(k, Source::PhysicalRegister(i)).unwrap_err();
    assert!((fpu.vals[i as usize].to_f64() - 3.78).abs() <= 0.00000000001);
    assert!((fpu.vals[j as usize].to_f64() - 2.718281828459045235360).abs() <= 0.00000000001);
    assert!((fpu.vals[k as usize].to_f64() - 3.1415926).abs() <= 0.000001);

    let above = k - 1;
    assert_eq!(fpu.tag.get_physical(above), TagValue::Empty as u8);
    fpu.assign_physical(above, Source::Value(&*SmallFloat::from(-2.6))).unwrap();
    assert_eq!(fpu.tag.get_physical(above), TagValue::NonZero as u8);
    assert!((fpu.vals[above as usize].to_f64() - -2.6).abs() <= 0.000001);

    fpu.push(Source::Value(&*SmallFloat::from(5.6))).unwrap_err();
    assert_eq!(fpu.status.get_top(), k);
    assert_eq!(fpu.tag.get_physical(above), TagValue::NonZero as u8);
    assert!((fpu.vals[k as usize].to_f64() - 3.1415926).abs() <= 0.000001);
    assert!((fpu.vals[above as usize].to_f64() - -2.6).abs() <= 0.000001);

    fpu.assign_physical(k, Source::PhysicalRegister(above)).unwrap();
    assert_eq!(fpu.status.get_top(), k);
    assert_eq!(fpu.tag.get_physical(above), TagValue::NonZero as u8);
    assert_eq!(fpu.tag.get_physical(k), TagValue::NonZero as u8);
    assert!((fpu.vals[k as usize].to_f64() - -2.6).abs() <= 0.000001);
    assert!((fpu.vals[above as usize].to_f64() - -2.6).abs() <= 0.000001);

    fpu.reset();
    for i in 0..8 {
        assert_eq!(fpu.tag.get_physical(i), TagValue::Empty as u8);
    }
    assert_eq!(fpu.status.get_top(), 0);

    fpu.assign_physical(0, Source::Value(&*SmallFloat::from(u64::MAX))).unwrap();
    assert_eq!(fpu.vals[0].to_integer().unwrap(), u64::MAX);
    assert_eq!(fpu.vals[0], u64::MAX);

    fpu.assign_physical(0, Source::Value(&*SmallFloat::from(i64::MAX))).unwrap();
    assert_eq!(fpu.vals[0].to_integer().unwrap(), i64::MAX);
    assert_eq!(fpu.vals[0], i64::MAX);

    fpu.assign_physical(0, Source::Value(&*SmallFloat::from(i64::MIN))).unwrap();
    assert_eq!(fpu.vals[0].to_integer().unwrap(), i64::MIN);
    assert_eq!(fpu.vals[0], i64::MIN);
}