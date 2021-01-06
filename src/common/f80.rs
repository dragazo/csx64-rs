//! Conversion utilities between `rug::Float` and an 80-bit binary representation used by the FPU.

use std::num::FpCategory;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::fmt::{self, LowerHex, UpperHex, Formatter};
use std::io::{self, Read, Write};
use rug::Float;
use rug::float::Special;
use rug::ops::{NegAssign};
use super::serialization::*;

#[cfg(test)]
use rug::float::SmallFloat;

pub const SIGNIFICANT_BITS: u32 = 64;
pub const EXPONENT_BITS: u32 = 15;

const EXPONENT_BIAS: i32 = (1 << (EXPONENT_BITS - 1)) - 1;

const EXPONENT_MAX: i32 = EXPONENT_BIAS as i32;
const EXPONENT_MIN: i32 = -EXPONENT_MAX;

// --------------------------------------------------------------------------------------------------------------------

pub const POSITIVE_ZERO: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
pub const NEGATIVE_ZERO: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80]);

pub const POSITIVE_NAN: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
pub const NEGATIVE_NAN: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);

pub const POSITIVE_INFINITY: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x7f]);
pub const NEGATIVE_INFINITY: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff]);

/// The highest-magnitude positive finite value.
pub const MAX: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7e]);
/// The highest-magnitude negative finite value.
pub const MIN: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xfe]);

/// The lowest-magnitude positive finite value.
pub const MIN_POSITIVE: F80 = F80([1, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
/// The lowest-magnitude negating finite value.
pub const MAX_NEGATIVE: F80 = F80([1, 0, 0, 0, 0, 0, 0, 0, 0, 0x80]);

/// Represents an 80-bit extended precision floating point number.
/// 
/// This type isn't technically a floating point type itself (no arithmetic operations are defined).
/// This is just meant to hold the binary representation of an 80-bit float for use in strongly typed conversions.
/// Note that values are thought to be 80-bit unsigned integers (sign bit is highest bit, followed by exp, then sig), but are stored little-endian.
/// 
/// There are 15 exponent bits and 64 significant bits.
/// This means that integer arithmetic performed using extended floats are precice up to the range of 64-bit unsigned integers.
/// Note that 80-bit floating point does not hide the leading bit, and therefore does not have subnormal values.
/// 
/// # Example
/// ```
/// # use csx64::common::f80::F80;
/// # use rug::Float;
/// // here we specify 64 significant bits.
/// // less is ok, more is also ok but would be lost in conversion to F80.
/// let float = Float::with_val(64, Float::parse("2.718281828459045235360").unwrap());
/// let f80 = F80::from(&float);
/// println!("encoded: {:x}", f80);
/// let back = Float::from(f80);
/// assert_eq!(float, back);
/// ```
#[derive(Clone, Copy, Debug)]
pub struct F80(pub [u8; 10]);
impl F80 {
    /// Converts the `F80` instance into a little-endian byte array.
    /// This is equivalent to accessing the wrapped value, but is defined for macro expansion convenience.
    pub fn to_le_bytes(self) -> [u8; 10] {
        self.0
    }
    /// Constructs an `F80` instance from a little-endian byte array.
    /// This is equivalent to wrapping the array, but is defined for macro expansion convenience.
    pub fn from_le_bytes(bytes: [u8; 10]) -> F80 {
        F80(bytes)
    }
    /// Classifies the current value.
    pub fn classify(&self) -> FpCategory {
        if self.0 == POSITIVE_ZERO.0 || self.0 == NEGATIVE_ZERO.0 { return FpCategory::Zero; }
        if self.0 == POSITIVE_INFINITY.0 || self.0 == NEGATIVE_INFINITY.0 { return FpCategory::Infinite; }
        if self.0[8] == 0xff && self.0[9] & 0x7f == 0x7f { return FpCategory::Nan; }
        if self.0[7] & 0x80 == 0 { return FpCategory::Subnormal; } // f80 doesn't hide a bit, so subnormal is just high bit of zero
        FpCategory::Normal
    }
}

impl BinaryWrite for F80 {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        f.write_all(&self.0)
    }
}
impl BinaryRead for F80 {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<F80> {
        let mut v = [0; 10];
        f.read_exact(&mut v)?;
        Ok(F80(v))
    }
}
#[test]
fn test_serial_f80() {
    let vals = &[POSITIVE_ZERO, NEGATIVE_ZERO, POSITIVE_NAN, NEGATIVE_NAN, POSITIVE_INFINITY, NEGATIVE_INFINITY, MIN, MAX, MIN_POSITIVE];
    let mut c = vec![];
    for v in vals {
        v.bin_write(&mut c).unwrap();
    }
    let mut c = c.as_slice();
    for v in vals {
        let res = F80::bin_read(&mut c).unwrap();
        assert_eq!(v.0, res.0);
    }
    u8::bin_read(&mut c).unwrap_err();
}

macro_rules! impl_disp {
    ($trait:ident [ $fmt:expr ]) => {
        impl $trait for F80 {
            fn fmt(&self, f: &mut Formatter) -> Result<(), fmt::Error> {
                for &v in self.0.iter().rev() {
                    write!(f, $fmt, v)?;
                }
                Ok(())
            }
        }
    }
}
impl_disp! { LowerHex["{:02x}"] }
impl_disp! { UpperHex["{:02X}"] }
#[test]
fn test_f80_disp() {
    let v = F80([1, 2, 0, 4, 5, 0x20, 0x21, 0x22, 0x23, 0xff]);
    assert_eq!(format!("{:x}", v), "ff232221200504000201");
    assert_eq!(format!("{:X}", v), "FF232221200504000201");
}

impl From<&Float> for F80 {
    fn from(value: &Float) -> F80 {
        match value.classify() {
            FpCategory::Nan => match value.is_sign_positive() {
                true => POSITIVE_NAN, // we arbitrarily elect to use all 1's for NaN significand
                false => NEGATIVE_NAN,
            }
            FpCategory::Infinite => match value.is_sign_positive() {
                true => POSITIVE_INFINITY,
                false => NEGATIVE_INFINITY,
            }
            FpCategory::Zero => match value.is_sign_positive() {
                true => POSITIVE_ZERO,
                false => NEGATIVE_ZERO,
            }
            FpCategory::Subnormal => unreachable!(), // rug float cannot be subnormal
            FpCategory::Normal => {
                let (mut sig, mut exp) = value.to_integer_exp().unwrap(); // deconstruct value in significant and exponent - unwrap safe because value is normal
                let is_negative = match sig.cmp0() { // convert sig to positive and store the sign bit
                    Ordering::Greater => false,
                    Ordering::Less => {
                        sig.neg_assign();
                        true
                    }
                    Ordering::Equal => unreachable!(), // we already handled zero case above, so this should never happen
                };
                debug_assert!(sig > 0);

                let sig_dif = sig.significant_bits() as i32 - SIGNIFICANT_BITS as i32;
                let round_up = sig_dif > 0 && sig.get_bit(sig_dif as u32 - 1); // get the rounding flag - last bit to be chopped off if we have too many bits
                if sig_dif != 0 { // if we don't have the right number of significant bits, change it so we do
                    sig >>= sig_dif; // rug nicely supports negative shift
                    exp += sig_dif;  // cancel out the change in exp
                }
                exp += SIGNIFICANT_BITS as i32 - 1; // account for the fact that we have an int rather than 1.ffff etc.
                debug_assert_eq!(sig.significant_bits(), SIGNIFICANT_BITS);
                if round_up {
                    sig += 1; // apply round up if needed and perform one final (trivial) shift if needed (only way this can happen is 11..11 + 1 => 100..00)
                    if sig.significant_bits() > SIGNIFICANT_BITS {
                        sig >>= 1;
                        exp += 1;
                    }
                }
                debug_assert_eq!(sig.significant_bits(), SIGNIFICANT_BITS);

                let mut sig: u64 = sig.to_u64().unwrap(); // sig is now guaranteed to fit in a u64
                if exp > EXPONENT_MAX { // exceeding max exponent leads to infinity
                    match is_negative {
                        true => return NEGATIVE_INFINITY,
                        false => return POSITIVE_INFINITY,
                    }
                }
                if exp < EXPONENT_MIN { // going below min exponent can be corrected as subnormal
                    let s = EXPONENT_MIN - exp;
                    if s < 64 { sig >>= s; } else { sig = 0; } // do a shift, but 64 or more always yields zero
                    exp = EXPONENT_MIN; // this fixes the problem to just be min exponent
                }
                exp += EXPONENT_BIAS; // apply the exponent bias
                debug_assert!(exp >= 0 && exp <= 0x7ffe);

                // we now have everything we need to piece the value together
                let mut v = [0; 10];
                v[0..8].copy_from_slice(&sig.to_le_bytes());
                v[8..10].copy_from_slice(&(exp as u16).to_le_bytes());
                if is_negative { v[9] |= 0x80; }
                F80(v)
            }
        }
    }
}
impl From<F80> for Float {
    fn from(value: F80) -> Float {
        let sig = u64::from_le_bytes(value.0[0..8].try_into().unwrap()); // extract sig portion as int
        let (is_negative, exp) = {
            let t = u16::from_le_bytes(value.0[8..10].try_into().unwrap());
            (t >= 0x8000, (t & 0x7fff) as i32) // extract neg flag and exponent field
        };
        let mut res = match exp {
            0x7fff => match sig { // all 1 is special (nan or infinity depending on sig)
                0 => Float::with_val(SIGNIFICANT_BITS, Special::Infinity),
                _ => Float::with_val(SIGNIFICANT_BITS, Special::Nan)
            }
            _ => { // otherwise is normal or subnormal, but because f80 doesn't hide the leading bit that's handled by the same logic
                let mut res = Float::with_val(SIGNIFICANT_BITS, sig); // construct the float based on sig
                res <<= (exp - EXPONENT_BIAS) - (SIGNIFICANT_BITS as i32 - 1); // apply the unbiased exponent and undo the effects of using int in previous step
                res
            }
        };
        if is_negative { res.neg_assign(); } // apply negative flag as final step
        res
    }
}

#[test]
fn test_f80_cvt() {
    let epsilon = Float::with_val(SIGNIFICANT_BITS, -4932).exp10(); // how close numbers must be in assertions
    assert!(epsilon > 0 && epsilon < f64::MIN_POSITIVE);

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::Infinity)).0, POSITIVE_INFINITY.0);
    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::NegInfinity)).0, NEGATIVE_INFINITY.0);

    assert!({ let v = Float::from(POSITIVE_INFINITY); v.is_infinite() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_INFINITY); v.is_infinite() && v.is_sign_negative() });

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::Nan)).0, POSITIVE_NAN.0);
    assert_eq!(F80::from(&-Float::with_val(SIGNIFICANT_BITS, Special::Nan)).0, NEGATIVE_NAN.0);

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::Nan)).classify(), FpCategory::Nan);
    assert_eq!(F80::from(&-Float::with_val(SIGNIFICANT_BITS, Special::Nan)).classify(), FpCategory::Nan);

    assert_eq!(F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]).classify(), FpCategory::Nan);
    assert_eq!(F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0xff, 0x7f]).classify(), FpCategory::Nan);
    assert_eq!(F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]).classify(), FpCategory::Nan);
    assert_eq!(F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0xff, 0xff]).classify(), FpCategory::Nan);

    assert!({ let v = Float::from(POSITIVE_NAN); v.is_nan() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_NAN); v.is_nan() && v.is_sign_negative() });

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::Zero)).0, POSITIVE_ZERO.0);
    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, Special::NegZero)).0, NEGATIVE_ZERO.0);

    assert!({ let v = Float::from(POSITIVE_ZERO); v.is_zero() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_ZERO); v.is_zero() && v.is_sign_negative() });

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, 1)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0x3f]);
    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, 2)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0x40]);

    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0x3f])); (v - Float::with_val(SIGNIFICANT_BITS, 1)).abs() < epsilon });
    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0x40])); (v - Float::with_val(SIGNIFICANT_BITS, 2)).abs() < epsilon });

    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, -1)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0xbf]);
    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, -2)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0xc0]);

    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0xbf])); (v - Float::with_val(SIGNIFICANT_BITS, -1)).abs() < epsilon });
    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0xc0])); (v - Float::with_val(SIGNIFICANT_BITS, -2)).abs() < epsilon });

    let tenth: Float = Float::with_val(SIGNIFICANT_BITS, 1) / 10;
    let neg_tenth: Float = Float::with_val(SIGNIFICANT_BITS, -1) / 10;
    assert_eq!(F80::from(&tenth).0, [0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0x3f]);
    assert_eq!(F80::from(&neg_tenth).0, [0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0xbf]);

    assert!({ let v = Float::from(F80([0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0x3f])); (v - tenth).abs() < epsilon });
    assert!({ let v = Float::from(F80([0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0xbf])); (v - neg_tenth).abs() < epsilon });

    let super_tenth: Float = Float::with_val(SIGNIFICANT_BITS + 5, 1) / 10;
    assert_eq!(F80::from(&super_tenth).0, [0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0x3f]);

    for p in -11356..=11356i32 {
        let f = Float::with_val(SIGNIFICANT_BITS, p).exp();
        let b = F80::from(&f);
        let ff = Float::from(b);
        if Float::with_val(SIGNIFICANT_BITS, &f - &ff).abs() >= epsilon {
            panic!("e^{} ({}) -> {:x} -> {}", p, f, b, ff);
        }
    }
    assert_eq!(F80::from(&Float::with_val(SIGNIFICANT_BITS, 11357).exp()).0, POSITIVE_INFINITY.0);
    assert!({ let v = Float::from(F80::from(&Float::with_val(SIGNIFICANT_BITS, 11357).exp())); v.is_infinite() && v.is_sign_positive() });

    assert!({ let v = Float::from(MIN_POSITIVE); v.is_finite() && !v.is_zero() && v.is_sign_positive() });
    assert_eq!(F80::from(&Float::from(MIN_POSITIVE)).0, MIN_POSITIVE.0);
    assert_eq!(F80::from(&Float::from(MIN_POSITIVE)).classify(), FpCategory::Subnormal);

    {
        let v: Float = Float::from(MIN_POSITIVE) / 2;
        let b = F80::from(&v);
        assert_eq!(b.0, POSITIVE_ZERO.0);
        assert_eq!(b.classify(), FpCategory::Zero);
    }
    {
        let v: Float = Float::from(MAX_NEGATIVE) / 2;
        let b = F80::from(&v);
        assert_eq!(b.0, NEGATIVE_ZERO.0);
        assert_eq!(b.classify(), FpCategory::Zero);
    }

    assert!({ let v = Float::from(MAX); v.is_finite() && !v.is_zero() && v.is_sign_positive() && v > f64::MAX });
    assert_eq!(F80::from(&Float::from(MAX)).0, MAX.0);
    assert_eq!(F80::from(&Float::from(MAX)).classify(), FpCategory::Normal);

    assert!({ let v = Float::from(MIN); v.is_finite() && !v.is_zero() && v.is_sign_negative() && v < f64::MIN });
    assert_eq!(F80::from(&Float::from(MIN)).0, MIN.0);
    assert_eq!(F80::from(&Float::from(MIN)).classify(), FpCategory::Normal);

    let almost_2 = Float::with_val(SIGNIFICANT_BITS + 20, 2) - Float::with_val(SIGNIFICANT_BITS + 20, -66).exp2();
    assert!(almost_2 < 2);
    assert!({ let mut v = almost_2.clone(); v.set_prec(SIGNIFICANT_BITS); v == 2 });
    assert_eq!(F80::from(&almost_2).0, F80::from(&*SmallFloat::from(2)).0);
}