//! Utilities for auto-overlapping binary sets.

use std::borrow::Cow;
use std::io::{self, Read, Write};
use std::iter::FusedIterator;
use std::slice;
use crate::common::serialization::*;

#[derive(Clone, Copy, Debug)]
pub struct SliceInfo {
    /// Index of the backing array.
    pub src: usize,
    /// Starting position in the backing array.
    pub start: usize,
    /// Length of the slice.
    pub length: usize,
}
impl BinaryWrite for SliceInfo {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.src.bin_write(f)?;
        self.start.bin_write(f)?;
        self.length.bin_write(f)
    }
}
impl BinaryRead for SliceInfo {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<SliceInfo> {
        let src = usize::bin_read(f)?;
        let start = usize::bin_read(f)?;
        let length = usize::bin_read(f)?;
        Ok(SliceInfo { src, start, length })
    }
}

/// An appendonly set of auto-overlapping binary slices.
/// 
/// In use, you add binary slices one at a time and it will attempt to create maximum overlapping.
/// Currently, it only guarantees that supersets and subsets will overlap.
/// It's theoretically possible to do cross-slice overlapping, but this would be complex and expensive.
/// 
/// Slices added to the set are guaranteed to remain in insertion order.
/// Moreover, the collection is appendonly, so once a slice is added it will remain at that index.
/// Iteration is guaranteed to maintain this ordering.
/// 
// # Example
// ```
// # use csx64::asm::binary_set::*;
// let mut b = BinarySet::new();
// b.add([1, 2, 3, 4].as_ref());     // insert first slice (backed by itself)
// b.add(vec![2, 3]);                // this one will overlap with previous
// assert_eq!(b.bytes(), 6);         // 6 bytes are stored (slices)
// assert_eq!(b.backing_bytes(), 4); // using only 4 backing bytes (internal data)
// ```
#[derive(Default, Clone, Debug)]
pub struct BinarySet {
    data: Vec<Vec<u8>>,     // the backing data
    slices: Vec<SliceInfo>, // effectively slices into top
}
impl BinaryWrite for BinarySet {
    fn bin_write<F: Write>(&self, f: &mut F) -> io::Result<()> {
        self.data.bin_write(f)?;
        self.slices.bin_write(f)
    }
}
impl BinaryRead for BinarySet {
    fn bin_read<F: Read>(f: &mut F) -> io::Result<BinarySet> {
        let data = BinaryRead::bin_read(f)?;
        let slices = BinaryRead::bin_read(f)?;
        Ok(BinarySet { data, slices })
    }
}

// ----------------------------------------------------------------------------

fn find_subregion(sup: &[u8], sub: &[u8]) -> Option<usize> {
    // look at windows in sup of length sub and return the first matching index if any
    for (i, w) in sup.windows(sub.len()).enumerate() {
        if w == sub {
            return Some(i)
        }
    }
    None // otherwise no subregion was found
}
#[test]
fn test_find_subregion() {
    assert_eq!(find_subregion(&[1, 2, 3], &[1]), Some(0));
    assert_eq!(find_subregion(&[1, 2, 3], &[2]), Some(1));
    assert_eq!(find_subregion(&[1, 2, 3], &[3]), Some(2));
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[2, 3]), Some(1));
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[2, 3, 3]), Some(1));
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[2, 3, 4]), Some(4));
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[2, 3, 4, 5]), None);
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[1, 2, 3, 3, 2, 3, 4]), Some(0));
    assert_eq!(find_subregion(&[1, 2, 3, 3, 2, 3, 4], &[1, 2, 3, 3, 2, 3, 4, 1]), None);
}

impl BinarySet {
    /// Constructs an empty set.
    pub fn new() -> Self {
        Default::default()
    }

    fn add_internal(&mut self, value: Cow<[u8]>) -> usize {
        assert!(!value.is_empty());

        // if an equivalent slice already exists, just refer to that
        for (i, other) in self.iter().enumerate() {
            if other == &*value { return i; }
        }

        let ret = self.slices.len(); // eventual return value

        // look for any data entry that value is a subregion of - if we find one we can use that as data source
        for (i, top) in self.data.iter().enumerate() {
            if let Some(start) = find_subregion(top, &*value) {
                self.slices.push(SliceInfo { src: i, start, length: value.len() });
                return ret;
            }
        }

        // if that didn't work, look for any data entry that is a subregion of value (i.e. containment the other way)
        for i in 0..self.data.len() {
            // if we found one, we can replace it with value
            if let Some(start) = find_subregion(&*value, &self.data[i]) {
                // replace it with value and update the starting position of any slices that referenced it
                self.data[i] = value.into_owned();
                for slice in self.slices.iter_mut() {
                    if slice.src == i { slice.start += start; }
                }

                // now we need to look through the data entries again and see if any of them are contained in value (the new, larger data entry)
                // we stopped on first that was a subset of value, so no need to tests 0..=i
                let mut j = i + 1;
                while j < self.data.len() {
                    // if data entry j is contained in value (entry i), we can remove j
                    if let Some(start) = find_subregion(&self.data[i], &self.data[j]) {
                        // get rid of j, redundant with i - use swap remove for efficiency
                        self.data.swap_remove(j);

                        // update all the slices to reflect the change
                        for slice in self.slices.iter_mut() {
                            // if it referenced the deleted entry (j), repoint it to value (i) and apply the start offset
                            if slice.src == j {
                                slice.src = i;
                                slice.start += start;
                            }
                            // if it referenced the moved entry (the one we used for swap remove), repoint it to j
                            else if slice.src == self.data.len() {
                                slice.src = j;
                            }
                        }
                    }
                    else { j += 1; } // only increment j if we didn't remove j
                }

                // and finally, add the slice info
                self.slices.push(SliceInfo { src: i, start: 0, length: self.data[i].len() });
                return ret;
            }
        }

        // if that also didn't work then we just have to add value as a new data entry
        let length = value.len();
        self.data.push(value.into_owned());
        self.slices.push(SliceInfo { src: self.data.len() - 1, start: 0, length });
        ret
    }

    /// Adds the specified slice to the set, panicing if empty.
    /// If an equivalent slice already exists, does nothing, otherwise adds `value` as a new slice.
    /// Returns the index of the pre-existing or new slice.
    pub fn add<'a, T>(&mut self, value: T) -> usize
    where T: Into<Cow<'a, [u8]>> 
    {
        self.add_internal(value.into())
    }

    /// Removes all content from the set.
    /// This is the only non-appendonly operation, and is just meant to support resource reuse.
    pub fn clear(&mut self) {
        self.data.clear();
        self.slices.clear();
    }
    /// Gets the number of slices contained in the set.
    pub fn len(&self) -> usize {
        self.slices.len()
    }
    /// Checks if the set is empty.
    pub fn is_empty(&self) -> bool {
        self.slices.is_empty()
    }

    /// Iterates over all of the slices contained in the set.
    pub fn iter(&self) -> Iter {
        Iter { data: &self.data, iter: self.slices.iter() }
    }
    /// Gets the slice at the specified index, or None if out of bounds.
    pub fn get(&self, index: usize) -> Option<&[u8]> {
        self.slices.get(index).map(|s| &self.data[s.src][s.start..s.start+s.length])
    }

    /// Gets the total number of bytes from distinct slices that were added to the set.
    pub fn bytes(&self) -> usize {
        self.slices.iter().fold(0, |v, s| v + s.length)
    }
    /// Gets the total number of bytes backing the stored slices.
    /// This is never larger than `bytes`.
    pub fn backing_bytes(&self) -> usize {
        self.data.iter().fold(0, |v, s| v + s.len())
    }

    /// Gets the collection of backing arrays and the collection of slices.
    pub fn decompose(self) -> (Vec<Vec<u8>>, Vec<SliceInfo>) {
        (self.data, self.slices)
    }
}
/// Iterates over the slices of a `BinarySet` in insertion order.
pub struct Iter<'a> {
    data: &'a [Vec<u8>],
    iter: slice::Iter<'a, SliceInfo>,
}
impl<'a> Iterator for Iter<'a> {
    type Item = &'a [u8];
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|s| &self.data[s.src][s.start..s.start+s.length])
    }
}
impl<'a> FusedIterator for Iter<'a> {}

#[test]
#[should_panic]
fn test_binary_set_empty_panic() {
    let mut s = BinarySet::new();
    s.add(vec![]);
}

#[test]
fn test_binary_set() {
    let mut s = BinarySet::new();
    assert_eq!(s.len(), 0);
    assert!(s.is_empty());
    assert_eq!(s.iter().count(), 0);
    assert_eq!(s.bytes(), 0);
    assert_eq!(s.backing_bytes(), 0);

    assert_eq!(s.add(vec![1, 2, 3]), 0);
    assert_eq!(s.len(), 1);
    assert!(!s.is_empty());
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref()]);
    assert_eq!(s.bytes(), 3);
    assert_eq!(s.backing_bytes(), 3);

    assert_eq!(s.add(vec![2, 3]), 1);
    assert_eq!(s.len(), 2);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref()]);
    assert_eq!(s.bytes(), 5);
    assert_eq!(s.backing_bytes(), 3);

    assert_eq!(s.add(vec![2, 3]), 1);
    assert_eq!(s.len(), 2);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref()]);
    assert_eq!(s.bytes(), 5);
    assert_eq!(s.backing_bytes(), 3);

    assert_eq!(s.add(vec![1, 2, 3]), 0);
    assert_eq!(s.len(), 2);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref()]);
    assert_eq!(s.bytes(), 5);
    assert_eq!(s.backing_bytes(), 3);

    assert_eq!(s.add(vec![2, 3, 4, 5]), 2);
    assert_eq!(s.len(), 3);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref(), [2, 3, 4, 5].as_ref()]);
    assert_eq!(s.bytes(), 9);
    assert_eq!(s.backing_bytes(), 7);

    assert_eq!(s.add(vec![2, 3, 4, 5]), 2);
    assert_eq!(s.len(), 3);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3].as_ref(), [2, 3, 4, 5].as_ref()]);
    assert_eq!(s.bytes(), 9);
    assert_eq!(s.backing_bytes(), 7);

    assert_eq!(s.add(vec![1, 2, 3, 4]), 3);
    assert_eq!(s.len(), 4);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref(), [1, 2, 3, 4].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3, 4].as_ref(), [2, 3, 4, 5].as_ref()]);
    assert_eq!(s.bytes(), 13);
    assert_eq!(s.backing_bytes(), 8);

    {
        let mut s = s.clone();
        assert_eq!(s.add(vec![255, 69, 1, 2, 3, 4, 5, 0, 0, 10, 20]), 4);
        assert_eq!(s.len(), 5);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref(), [1, 2, 3, 4].as_ref(),
            [255, 69, 1, 2, 3, 4, 5, 0, 0, 10, 20].as_ref()]);
        assert_eq!(s.data, &[[255, 69, 1, 2, 3, 4, 5, 0, 0, 10, 20].as_ref()]);
        assert_eq!(s.bytes(), 24);
        assert_eq!(s.backing_bytes(), 11);
    }
    {
        let mut s = s.clone();
        assert_eq!(s.add(vec![2, 3, 4, 5, 0, 0, 10, 20]), 4);
        assert_eq!(s.len(), 5);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref(), [1, 2, 3, 4].as_ref(),
            [2, 3, 4, 5, 0, 0, 10, 20].as_ref()]);
            assert_eq!(s.data, &[[1, 2, 3, 4].as_ref(), [2, 3, 4, 5, 0, 0, 10, 20].as_ref()]);
            assert_eq!(s.bytes(), 21);
            assert_eq!(s.backing_bytes(), 12);
    }
    {
        let mut s = s.clone();
        assert_eq!(s.add(vec![255, 69, 1, 2, 3, 4]), 4);
        assert_eq!(s.len(), 5);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[1, 2, 3].as_ref(), [2, 3].as_ref(), [2, 3, 4, 5].as_ref(), [1, 2, 3, 4].as_ref(),
            [255, 69, 1, 2, 3, 4].as_ref()]);
        assert_eq!(s.data, &[[255, 69, 1, 2, 3, 4].as_ref(), [2, 3, 4, 5].as_ref()]);
        assert_eq!(s.bytes(), 19);
        assert_eq!(s.backing_bytes(), 10);
    }

    s.clear();
    assert_eq!(s.len(), 0);
    assert!(s.is_empty());
    assert_eq!(s.iter().count(), 0);
    assert_eq!(s.bytes(), 0);
    assert_eq!(s.backing_bytes(), 0);

    assert_eq!(s.add(vec![6, 6, 6]), 0);
    assert_eq!(s.len(), 1);
    assert!(!s.is_empty());
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[6, 6, 6].as_ref()]);
    assert_eq!(s.data, &[[6, 6, 6].as_ref()]);
    assert_eq!(s.bytes(), 3);
    assert_eq!(s.backing_bytes(), 3);

    assert_eq!(s.add(vec![2, 3, 4]), 1);
    assert_eq!(s.len(), 2);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[6, 6, 6].as_ref(), [2, 3, 4].as_ref()]);
    assert_eq!(s.data, &[[6, 6, 6].as_ref(), [2, 3, 4].as_ref()]);
    assert_eq!(s.bytes(), 6);
    assert_eq!(s.backing_bytes(), 6);

    assert_eq!(s.add(vec![2, 3]), 2);
    assert_eq!(s.len(), 3);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[6, 6, 6].as_ref(), [2, 3, 4].as_ref(), [2, 3].as_ref()]);
    assert_eq!(s.data, &[[6, 6, 6].as_ref(), [2, 3, 4].as_ref()]);
    assert_eq!(s.bytes(), 8);
    assert_eq!(s.backing_bytes(), 6);

    assert_eq!(s.add(vec![1, 2, 3, 6, 6, 6]), 3);
    assert_eq!(s.len(), 4);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[6, 6, 6].as_ref(), [2, 3, 4].as_ref(), [2, 3].as_ref(), [1, 2, 3, 6, 6, 6].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3, 6, 6, 6].as_ref(), [2, 3, 4].as_ref()]);
    assert_eq!(s.bytes(), 14);
    assert_eq!(s.backing_bytes(), 9);

    assert_eq!(s.add(vec![2, 3]), 2);
    assert_eq!(s.len(), 4);
    assert_eq!(s.iter().collect::<Vec<_>>(), vec![[6, 6, 6].as_ref(), [2, 3, 4].as_ref(), [2, 3].as_ref(), [1, 2, 3, 6, 6, 6].as_ref()]);
    assert_eq!(s.data, &[[1, 2, 3, 6, 6, 6].as_ref(), [2, 3, 4].as_ref()]);
    assert_eq!(s.bytes(), 14);
    assert_eq!(s.backing_bytes(), 9);

    {
        let mut s = BinarySet::new();
        assert_eq!(s.add(vec![0]), 0);
        assert_eq!(s.add(vec![1]), 1);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[0].as_ref(), [1].as_ref()]);
        assert_eq!(s.data, vec![[0].as_ref(), [1].as_ref()]);
        assert_eq!(s.add(vec![0, 1]), 2);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[0].as_ref(), [1].as_ref(), [0, 1].as_ref()]);
        assert_eq!(s.data, vec![[0, 1].as_ref()]);
    }
    {
        let mut s = BinarySet::new();
        assert_eq!(s.add(vec![0]), 0);
        assert_eq!(s.add(vec![1]), 1);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[0].as_ref(), [1].as_ref()]);
        assert_eq!(s.data, vec![[0].as_ref(), [1].as_ref()]);
        assert_eq!(s.add(vec![1, 0]), 2);
        assert_eq!(s.iter().collect::<Vec<_>>(), vec![[0].as_ref(), [1].as_ref(), [1, 0].as_ref()]);
        assert_eq!(s.data, vec![[1, 0].as_ref()]);
    }
}