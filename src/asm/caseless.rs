use std::cmp::Ordering;
use std::fmt;

#[cfg(test)]
use std::collections::BTreeSet;

fn cmp_ignore_ascii_case(a: &str, b: &str) -> Ordering {
    let (mut a, mut b) = (a.chars(), b.chars());
    loop {
        match (a.next(), b.next()) {
            (Some(a), Some(b)) => match a.to_ascii_uppercase().cmp(&b.to_ascii_uppercase()) {
                Ordering::Greater => return Ordering::Greater,
                Ordering::Less => return Ordering::Less,
                Ordering::Equal => (),
            }
            (None, Some(_)) => return Ordering::Less,
            (Some(_), None) => return Ordering::Greater,
            (None, None) => return Ordering::Equal,
        }
    }
}

/// An ASCII-case-insensitive wrapper for strings.
#[derive(Clone, Copy, Debug)]
pub struct Caseless<'a>(pub &'a str);

impl PartialEq<Caseless<'_>> for Caseless<'_> {
    fn eq(&self, other: &Caseless<'_>) -> bool {
        self.0.eq_ignore_ascii_case(other.0)
    }
}
impl Eq for Caseless<'_> {}

impl Ord for Caseless<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_ignore_ascii_case(self.0, other.0)
    }
}
impl PartialOrd<Caseless<'_>> for Caseless<'_> {
    fn partial_cmp(&self, other: &Caseless<'_>) -> Option<Ordering> {
        Some(cmp_ignore_ascii_case(self.0, other.0))
    }
}

impl fmt::Display for Caseless<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[test]
fn test_caseless() {
    assert_eq!(Caseless("hello"), Caseless("hello"));
    assert_eq!(Caseless("HeLLo"), Caseless("hello"));

    assert_ne!(Caseless("hello"), Caseless("hellod"));
    assert_ne!(Caseless("HeLLo"), Caseless("hellod"));

    assert!(Caseless("abc") < Caseless("BCD"));
    assert!(Caseless("ABC") < Caseless("bcd"));

    assert!(Caseless("ABC") < Caseless("abcd"));
    assert!(Caseless("abc") < Caseless("ABCD"));

    assert!(Caseless("ABCDE") > Caseless("abcd"));
    assert!(Caseless("abcde") > Caseless("ABCD"));

    assert!(Caseless("DQ") != Caseless("DX"));
    assert!(Caseless("DQ") < Caseless("DX"));

    {
        let mut s = BTreeSet::new();
        s.insert(Caseless("hello"));
        assert!(s.contains(&Caseless("HellO")));
        assert!(!s.contains(&Caseless("HellfO")));
        assert!(!s.insert(Caseless("hEllo")));
    }
}