//! Conversion utilities between `rug::Float` and an 80-bit binary representation.
//! 
//! This is used to support reading/writing extended precision fp values for `tword` loads in the FPU.

use std::num::FpCategory;
use std::cmp::Ordering;
use std::convert::TryInto;
use std::fmt::{self, LowerHex, UpperHex, Formatter};
use rug::Float;
use rug::float::Special;
use rug::ops::{NegAssign};

const SIGNIFICANT_BITS: u32 = 64;
const EXPONENT_BITS: u32 = 15;

const EXPONENT_BIAS: i32 = (1 << (EXPONENT_BITS - 1)) - 1;

const EXPONENT_MAX: i32 = EXPONENT_BIAS as i32;
const EXPONENT_MIN: i32 = 1 - EXPONENT_MAX;

// --------------------------------------------------------------------------------------------------------------------

pub const POSITIVE_ZERO: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);
pub const NEGATIVE_ZERO: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0, 0x80]);

pub const POSITIVE_NAN: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]);
pub const NEGATIVE_NAN: F80 = F80([0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);

pub const POSITIVE_INFINITY: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0x7f]);
pub const NEGATIVE_INFINITY: F80 = F80([0, 0, 0, 0, 0, 0, 0, 0, 0xff, 0xff]);

/// Represents an 80-bit extended precision floating point number.
/// 
/// This type isn't technically a floating point type itself (no arithmetic operations are defined).
/// This is just meant to hold the binary representation of an 80-bit float for use in strongly typed conversions.
/// Note that values are thought to be 80-bit unsigned integers (sign bit is highest bit, followed by exp, then sig), but are stored little-endian.
#[derive(Clone, Copy, Debug)]
pub struct F80(pub [u8; 10]);

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

impl From<Float> for F80 {
    fn from(value: Float) -> F80 {
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
            FpCategory::Subnormal => unreachable!(), // rug types cannot be subnormal
            FpCategory::Normal => {
                let (mut sig, mut exp) = value.to_integer_exp().unwrap(); // unwrap safe because value is normal
                let is_positive = match sig.cmp0() { // convert sig to positive and store the sign bit
                    Ordering::Greater => true,
                    Ordering::Less => {
                        sig.neg_assign();
                        false
                    }
                    Ordering::Equal => unreachable!(), // we already handled zero case above, so this should never happen
                };

                let sig_dif = sig.significant_bits() as i32 - SIGNIFICANT_BITS as i32;
                if sig_dif != 0 { // if we don't have the right number of significant bits, change it so we do
                    sig >>= sig_dif; // rug nicely supports negative shift
                    exp += sig_dif;  // cancel out the change in exp
                }
                exp += SIGNIFICANT_BITS as i32 - 1; // account for the fact that we have an int rather and a 1.ffff etc.

                let mut sig: u64 = sig.to_u64().unwrap(); // sig is now guaranteed to fit in a u64
                if exp > EXPONENT_MAX { // exceeding max exponent leads to infinity
                    match is_positive {
                        true => return POSITIVE_INFINITY,
                        false => return NEGATIVE_INFINITY,
                    }
                }
                if exp < EXPONENT_MIN { // going below min exponent can be corrected (but we don't currently support subnormal)
                    let s = EXPONENT_MIN - exp;
                    if s < 64 { sig >>= s; } else { sig = 0; } // do a shift, but 64 or more always yields zero
                    exp = EXPONENT_MIN; // this fixes the problem to just be min exponent
                }
                exp += EXPONENT_BIAS; // apply the exponent bias
                debug_assert!(exp >= 1 && exp <= 0x7ffe);

                // we now have everything we need to piece the value together
                let mut v: [u8; 10] = [0; 10];
                v[0..8].copy_from_slice(&sig.to_le_bytes());
                v[8..10].copy_from_slice(&(exp as u16).to_le_bytes());
                if !is_positive { v[9] |= 0x80; }

                F80(v) // and we're done
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
            0 => Float::new(SIGNIFICANT_BITS), // all 0 is subnormal - we don't support this yet, so just give back a zero
            0x7fff => match sig { // all 1 is special (nan or infinity depending on sig)
                0 => Float::with_val(SIGNIFICANT_BITS, Special::Infinity),
                _ => Float::with_val(SIGNIFICANT_BITS, Special::Nan)
            }
            _ => {
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

    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, Special::Infinity)).0, POSITIVE_INFINITY.0);
    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, Special::NegInfinity)).0, NEGATIVE_INFINITY.0);

    assert!({ let v = Float::from(POSITIVE_INFINITY); v.is_infinite() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_INFINITY); v.is_infinite() && v.is_sign_negative() });

    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, Special::Nan)).0, POSITIVE_NAN.0);
    assert_eq!(F80::from(-Float::with_val(SIGNIFICANT_BITS, Special::Nan)).0, NEGATIVE_NAN.0);

    assert!({ let v = Float::from(POSITIVE_NAN); v.is_nan() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_NAN); v.is_nan() && v.is_sign_negative() });

    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, Special::Zero)).0, POSITIVE_ZERO.0);
    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, Special::NegZero)).0, NEGATIVE_ZERO.0);

    assert!({ let v = Float::from(POSITIVE_ZERO); v.is_zero() && v.is_sign_positive() });
    assert!({ let v = Float::from(NEGATIVE_ZERO); v.is_zero() && v.is_sign_negative() });

    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, 1)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0x3f]);
    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, 2)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0x40]);

    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0x3f])); (v - Float::with_val(SIGNIFICANT_BITS, 1)).abs() < epsilon });
    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0x40])); (v - Float::with_val(SIGNIFICANT_BITS, 2)).abs() < epsilon });

    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, -1)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0xbf]);
    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, -2)).0, [0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0xc0]);

    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0xff, 0xbf])); (v - Float::with_val(SIGNIFICANT_BITS, -1)).abs() < epsilon });
    assert!({ let v = Float::from(F80([0, 0, 0, 0, 0, 0, 0, 0x80, 0x00, 0xc0])); (v - Float::with_val(SIGNIFICANT_BITS, -2)).abs() < epsilon });

    let tenth: Float = Float::with_val(SIGNIFICANT_BITS, 1) / 10;
    let neg_tenth: Float = Float::with_val(SIGNIFICANT_BITS, -1) / 10;
    assert_eq!(F80::from(tenth.clone()).0, [0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0x3f]);
    assert_eq!(F80::from(neg_tenth.clone()).0, [0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0xbf]);

    assert!({ let v = Float::from(F80([0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0x3f])); (v - tenth).abs() < epsilon });
    assert!({ let v = Float::from(F80([0xcd, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xcc, 0xfb, 0xbf])); (v - neg_tenth).abs() < epsilon });

    for p in -11356..=11356i32 {
        let f = Float::with_val(SIGNIFICANT_BITS, p).exp();
        let b = F80::from(f.clone());
        let ff = Float::from(b);
        if Float::with_val(SIGNIFICANT_BITS, &f - &ff).abs() >= epsilon {
            panic!("e^{} ({}) -> {:x} -> {}", p, f, b, ff);
        }
    }
    assert_eq!(F80::from(Float::with_val(SIGNIFICANT_BITS, 11357).exp()).0, POSITIVE_INFINITY.0);
    assert!({ let v = Float::from(F80::from(Float::with_val(SIGNIFICANT_BITS, 11357).exp())); v.is_infinite() && v.is_sign_positive() });
}