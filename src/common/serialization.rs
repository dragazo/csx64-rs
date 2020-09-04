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
int_impl!(u64, u32, u16, i64, i32, i16, i8);

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

impl<T: BinaryWrite> BinaryWrite for Option<T> {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        match self {
            None => 0u8.bin_write(f),
            Some(val) => {
                1u8.bin_write(f)?;
                val.bin_write(f)
            }
        }
    }
}
impl<T: BinaryRead> BinaryRead for Option<T> {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<Option<T>> {
        match u8::bin_read(f)? {
            0 => Ok(None),
            1 => Ok(Some(T::bin_read(f)?)),
            _ => Err(io::ErrorKind::InvalidData.into()),
        }
    }
}
