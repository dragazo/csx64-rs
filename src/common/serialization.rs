//! Utilities for representing values in cross-platform binary.
//! 
//! It is intended that all implementors use little-endian byte ordering for multi-byte values, but this is not strictly required.
//!
//! `BinaryRead` and `BinaryWrite` are the two main features of this module.
//! They are implemented for all integer primitives with the notably exception of `u8`.
//! This is because stable rust does not currently support specialization, meaning the blanket implementations
//! for `[T]` and `Vec<T>` would otherwise conflict with the performance-based implementations for `[u8]` and `Vec<u8>`.
//! To support the same interface (but not the same trait), `u8` implements `TrivialBinaryRead` and `TrivialBinaryWrite`.
//! This is typically not an issue, as arrays are the only common container for bytes.
//! 
//! # Example
//! ```
//! # use csx64::common::serialization::*;
//! # use std::io::Cursor;
//! let mut f = Cursor::new(Vec::new());
//! "hello world".bin_write(&mut f).unwrap();
//! f.set_position(0);
//! assert_eq!(String::bin_read(&mut f).unwrap(), "hello world");
//! ```

use std::io::{self, Read, Write};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::{mem, cmp};
use std::num::FpCategory;
use rug::{Float, float::Special, ops::NegAssign};
use rug::{Integer, integer::Order};

#[cfg(test)]
use std::io::Cursor;

/// Denotes that a type can be encoded as cross-platform binary.
pub trait BinaryWrite {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()>;
}
/// Denotes that a type can be decoded from cross-platform binary.
pub trait BinaryRead: Sized {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self>;
}

/// Denotes that a type can be trivially encoded as cross-platform binary.
pub trait TrivialBinaryWrite {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()>;
}
/// Denotes that a type can be trivially decoded from cross-platform binary.
pub trait TrivialBinaryRead: Sized {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self>;
}

impl TrivialBinaryWrite for u8 {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        f.write_all(&[*self])
    }
}
impl TrivialBinaryRead for u8 {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
        let mut buf = [0];
        f.read_exact(&mut buf)?;
        Ok(buf[0])
    }
}

macro_rules! int_impl {
    ($($type:ty),+) => {
        $(impl BinaryWrite for $type {
            fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
                f.write_all(&self.to_le_bytes())
            }
        }
        impl BinaryRead for $type {
            fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
                let mut bytes = [0; std::mem::size_of::<Self>()];
                f.read_exact(&mut bytes)?;
                Ok(Self::from_le_bytes(bytes))
            }
        })+
    }
}
int_impl!(u64, u32, u16, i64, i32, i16, i8, f64, f32);

macro_rules! extended_int_impl {
    ($($type:ty => $extended:ty),+) => {
        $(impl BinaryWrite for $type {
            fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
                (*self as $extended).bin_write(f)
            }
        }
        impl BinaryRead for $type {
            fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
                let val = <$extended>::bin_read(f)?;
                if val as $type as $extended != val {
                    return Err(io::ErrorKind::InvalidData.into());
                }
                Ok(val as $type)
            }
        })*
    }
}
extended_int_impl!(usize => u64, isize => i64);

#[test]
fn test_serialize_int() {
    let vals = [u64::MIN, u64::MAX, 0xdeadbeefdeadbeef, 0x0102030405060708];
    let mut cursor = Cursor::new(Vec::with_capacity(1024));
    macro_rules! test_for {
        ($($type:ty),+) => {{
            for &x in vals.iter() {
                $({
                    (x as $type).bin_write(&mut cursor).unwrap();
                })*
            }
            cursor.set_position(0);
            for &x in vals.iter() {
                $({
                let v = <$type>::bin_read(&mut cursor).unwrap();
                assert_eq!(v, x as $type);
                })*
            }
        }}
    }
    test_for!(u64, u32, u16, u8, i64, i32, i16, i8, isize, usize)
}
#[test]
#[cfg(target_pointer_width = "32")]
fn test_serialize_corrupt_usize() {
    let mut cursor = Cursor::new(Vec::with_capacity(8));
    0x385782usize.bin_write(&mut cursor).unwrap();
    cursor.set_position(7);
    cursor.write_all(&[1]).unwrap();
    cursor.set_position(0);
    match usize::bin_read(&mut cursor) {
        Err(e) if e.kind() == io::ErrorKind::InvalidData => (),
        _ => panic!("didn't fail"),
    }
}
#[test]
#[should_panic]
#[cfg(target_pointer_width = "32")]
fn test_serialize_corrupt_isize() {
    for &val in &[0x385782isize, -0x385782isize] {
        let mut cursor = Cursor::new(Vec::with_capacity(8));
        val.bin_write(&mut cursor).unwrap();
        cursor.set_position(7);
        cursor.write_all(&[1]).unwrap();
        cursor.set_position(0);
        match isize::bin_read(&mut cursor) {
            Err(e) if e.kind() == io::ErrorKind::InvalidData => (),
            _ => panic!("didn't fail for {}", val),
        }
    }
}

macro_rules! impl_tuple {
    ($($t:ident : $v:ident),+ => $($i:tt),+) => {
        impl<$($t),+> BinaryWrite for ($($t),+) where $($t: BinaryWrite),+ {
            fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
                $(self.$i.bin_write(f)?;)+
                Ok(())
            }
        }
        impl<$($t),+> BinaryRead for ($($t),+) where $($t: BinaryRead),+ {
            fn bin_read<F: Read>(f: &mut F) -> io::Result<($($t),+)> {
                $(let $v: $t = BinaryRead::bin_read(f)?;)+
                Ok(($($v),+))
            }
        }
    }
}

impl_tuple! { T0:t0, T1:t1 => 0, 1 }

impl BinaryWrite for [u8] {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.len().bin_write(f)?; // write a length prefix
        f.write_all(self)         // then dump all the content
    }
}
impl BinaryWrite for Vec<u8> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.as_slice().bin_write(f)
    }
}
impl BinaryRead for Vec<u8> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Vec<u8>> {
        let len = usize::bin_read(f)?; // read the length prefix
        let mut res = Vec::with_capacity(cmp::min(len, 1024 * 1024)); // allocate at most 1MB (in case of corrupted data)
        let mut buf = vec![0; cmp::min(len, 1024)]; // read blocks of 1KB at a time
        let buf_len = buf.len();
        while res.len() < len {
            let count = f.read(&mut buf[0..cmp::min(len - res.len(), buf_len)])?;
            res.extend_from_slice(&buf[0..count]);
        }
        Ok(res)
    }
}

impl BinaryWrite for str {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.as_bytes().bin_write(f)
    }
}
impl BinaryWrite for String {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.as_str().bin_write(f)
    }
}
impl BinaryRead for String {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<String> {
        match String::from_utf8(BinaryRead::bin_read(f)?) {
            Ok(s) => Ok(s),
            Err(_) => Err(io::ErrorKind::InvalidData.into())
        }
    }
}

impl<T: BinaryWrite> BinaryWrite for Box<T> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.as_ref().bin_write(f)
    }
}
impl<T: BinaryRead> BinaryRead for Box<T> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Box<T>> {
        Ok(Box::new(T::bin_read(f)?))
    }
}

/// Note that this immutably borrows the contents at runtime.
impl<T: BinaryWrite> BinaryWrite for RefCell<T> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.borrow().bin_write(f)
    }
}
impl<T: BinaryRead> BinaryRead for RefCell<T> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<RefCell<T>> {
        Ok(RefCell::new(T::bin_read(f)?))
    }
}

impl<T: BinaryWrite> BinaryWrite for [T] {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.len().bin_write(f)?; // write a length prefix
        for item in self.iter() {
            item.bin_write(f)?; // then dump all the content
        }
        Ok(())
    }
}
impl<T: BinaryWrite> BinaryWrite for Vec<T> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.as_slice().bin_write(f)
    }
}
impl<T: BinaryRead> BinaryRead for Vec<T> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Vec<T>> {
        let len = usize::bin_read(f)?; // read the length prefix
        let mut res = Vec::with_capacity(cmp::min(len, 1024 * 1024 / mem::size_of::<T>())); // allocate some space (not all in case of corrupted data)
        for _ in 0..len {
            res.push(T::bin_read(f)?); // read exactly len items
        }
        Ok(res)
    }
}

impl<K: BinaryWrite, V: BinaryWrite> BinaryWrite for HashMap<K, V> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.len().bin_write(f)?; // write a length prefix
        for (k, v) in self.iter() {
            k.bin_write(f)?; // then dump all the content
            v.bin_write(f)?;
        }
        Ok(())
    }
}
impl<K: BinaryRead + Hash + Eq, V: BinaryRead> BinaryRead for HashMap<K, V> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
        let len = usize::bin_read(f)?; // read the length prefix
        let mut res = HashMap::with_capacity(cmp::min(len, 1024 * 1024 / (mem::size_of::<K>() + mem::size_of::<V>()))); // allocate some space (not all, in case of corrupted data)
        for _ in 0..len {
            let key = K::bin_read(f)?;
            let value = V::bin_read(f)?;
            if let Some(_) = res.insert(key, value) { // duplicate keys means corrupted data
                return Err(io::ErrorKind::InvalidData.into());
            }
        }
        Ok(res)
    }
}

impl<T: BinaryWrite> BinaryWrite for HashSet<T> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.len().bin_write(f)?; // write a length prefix
        for v in self.iter() {
            v.bin_write(f)?; // then dump all the content
        }
        Ok(())
    }
}
impl<T: BinaryRead + Hash + Eq> BinaryRead for HashSet<T> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Self> {
        let len = usize::bin_read(f)?; // read the length prefix
        let mut res = HashSet::with_capacity(cmp::min(len, 1024 * 1024 / mem::size_of::<T>())); // allocate some space (not all, in case of corrupted data)
        for _ in 0..len {
            if !res.insert(T::bin_read(f)?) {
                return Err(io::ErrorKind::InvalidData.into());
            }
        }
        Ok(res)
    }
}

impl BinaryWrite for Integer {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.to_digits::<u8>(Order::LsfLe).bin_write(f)
    }
}
impl BinaryRead for Integer {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Integer> {
        Ok(Integer::from_digits(&Vec::<u8>::bin_read(f)?, Order::LsfLe))
    }
}

impl BinaryWrite for Float {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        let is_negative = self.is_sign_negative();
        let prec = self.prec();

        prec.bin_write(f)?;
        match self.classify() {
            FpCategory::Nan => match is_negative {
                false => 0u8.bin_write(f),
                true => 1u8.bin_write(f),
            }
            FpCategory::Infinite => match is_negative {
                false => 2u8.bin_write(f),
                true => 3u8.bin_write(f),
            }
            FpCategory::Zero => match is_negative {
                false => 4u8.bin_write(f),
                true => 5u8.bin_write(f),
            }
            FpCategory::Subnormal => unreachable!(), // rug float cannot be subnormal
            FpCategory::Normal => {
                let (mut sig, mut exp) = self.to_integer_exp().unwrap(); // extract sig/exp and convert sig to positive
                if is_negative { sig.neg_assign(); }
                debug_assert!(sig > 0);

                let trailing_zeros = sig.find_one(0).unwrap(); // for minimal storage, we'll chop off trailing zeros
                sig >>= trailing_zeros;
                exp += trailing_zeros as i32;

                match is_negative {
                    false => 6u8.bin_write(f)?,
                    true => 7u8.bin_write(f)?,
                }
                exp.bin_write(f)?;
                sig.bin_write(f)
            }
        }
    }
}
impl BinaryRead for Float {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Float> {
        let prec = BinaryRead::bin_read(f)?;
        let prefix = u8::bin_read(f)?;
        let res = match prefix {
            0 => Float::with_val(prec, Special::Nan),
            1 => -Float::with_val(prec, Special::Nan),

            2 => Float::with_val(prec, Special::Infinity),
            3 => Float::with_val(prec, Special::NegInfinity),

            4 => Float::with_val(prec, Special::Zero),
            5 => Float::with_val(prec, Special::NegZero),

            6 | 7 => {
                let exp = i32::bin_read(f)?;
                let sig = Integer::bin_read(f)?;
                let mut v = Float::with_val(prec, sig) << exp;
                if prefix == 7 { v.neg_assign() }
                v
            }

            _ => return Err(io::ErrorKind::InvalidData.into()),
        };
        Ok(res)
    }
}
#[test]
fn test_serial_float() {
    let vals = &[
        Float::with_val(78, Special::Zero),
        Float::with_val(43, Special::NegZero),
        Float::with_val(53, Special::Infinity),
        Float::with_val(66, Special::NegInfinity),
        Float::with_val(102, Special::Nan),
        -Float::with_val(12, Special::Nan),
        Float::with_val(150, 1) / 10,
        Float::with_val(15, -1) / 10,
        Float::with_val(76, 1) << rug::float::exp_max(),
        Float::with_val(72, -1) << rug::float::exp_min(),
    ];
    let mut c = Cursor::new(vec![]);
    for v in vals {
        v.bin_write(&mut c).unwrap();
    }
    c.set_position(0);
    for v in vals {
        let r = Float::bin_read(&mut c).unwrap();
        assert_eq!(r.prec(), v.prec());
        assert_eq!(r.is_sign_negative(), v.is_sign_negative());
        assert_eq!(r.classify(), v.classify());
        if !r.is_nan() { assert_eq!(&r, v); }
    }
}