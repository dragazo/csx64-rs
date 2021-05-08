use std::fmt;

/// Returns the quotient and remainder of `a` divided by `b`.
pub(crate) fn quotient_and_remainder<T>(a: T, b: T) -> (T, T) where T: std::ops::Div<Output = T> + std::ops::Rem<Output = T> + Copy {
    (a / b, a % b)
}

pub(crate) struct Punctuated<'a, T> { 
    vals: &'a [T],
    sep: &'static str,
    sep_special: &'static str,
}
impl<'a, T> Punctuated<'a, T> {
    pub(crate) fn or(vals: &'a [T]) -> Self {
        Self { vals, sep: ", ", sep_special: "or " }
    }
    pub(crate) fn and(vals: &'a [T]) -> Self {
        Self { vals, sep: ", ", sep_special: "and " }
    }
    pub(crate) fn join(vals: &'a [T], sep: &'static str) -> Self {
        Self { vals, sep, sep_special: "" }
    }
}
impl<'a, T: fmt::Display> fmt::Display for Punctuated<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.vals {
            [] => Ok(()),
            [x] => write!(f, "{}", x),
            [x, y] => {
                if self.sep_special.is_empty() { write!(f, "{}{}{}", x, self.sep, y) }
                else { write!(f, "{} {}{}", x, self.sep_special, y) }
            }
            [prev @ .., last] => {
                for x in prev {
                    write!(f, "{}{}", x, self.sep)?;
                }
                write!(f, "{}{}", self.sep_special, last)
            }
        }
    }
}
impl<'a, T: fmt::Debug> fmt::Debug for Punctuated<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.vals {
            [] => Ok(()),
            [x] => write!(f, "{:?}", x),
            [x, y] => {
                if self.sep_special.is_empty() { write!(f, "{:?}{}{:?}", x, self.sep, y) }
                else { write!(f, "{:?} {}{:?}", x, self.sep_special, y) }
            }
            [prev @ .., last] => {
                for x in prev {
                    write!(f, "{:?}{}", x, self.sep)?;
                }
                write!(f, "{}{:?}", self.sep_special, last)
            }
        }
    }
}
#[test]
fn test_comma_chain() {
    assert_eq!(format!("{}", Punctuated::or(&[] as &[i32])), "");
    assert_eq!(format!("{}", Punctuated::or(&[8])), "8");
    assert_eq!(format!("{}", Punctuated::or(&[8, 7])), "8 or 7");
    assert_eq!(format!("{}", Punctuated::or(&[8, 7, 5])), "8, 7, or 5");
    assert_eq!(format!("{}", Punctuated::or(&[8, 7, 5, 2, 1])), "8, 7, 5, 2, or 1");

    assert_eq!(format!("{}", Punctuated::and(&[] as &[i32])), "");
    assert_eq!(format!("{}", Punctuated::and(&[8])), "8");
    assert_eq!(format!("{}", Punctuated::and(&[8, 7])), "8 and 7");
    assert_eq!(format!("{}", Punctuated::and(&[8, 7, 5])), "8, 7, and 5");
    assert_eq!(format!("{}", Punctuated::and(&[8, 7, 5, 2, 1])), "8, 7, 5, 2, and 1");

    assert_eq!(format!("{}", Punctuated::join(&[] as &[i32], ", ")), "");
    assert_eq!(format!("{}", Punctuated::join(&[8], ", ")), "8");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7], ", ")), "8, 7");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7, 5], ", ")), "8, 7, 5");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7, 5, 2, 1], ", ")), "8, 7, 5, 2, 1");

    assert_eq!(format!("{}", Punctuated::join(&[] as &[i32], ",")), "");
    assert_eq!(format!("{}", Punctuated::join(&[8], ",")), "8");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7], ",")), "8,7");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7, 5], ",")), "8,7,5");
    assert_eq!(format!("{}", Punctuated::join(&[8, 7, 5, 2, 1], ",")), "8,7,5,2,1");

    // -------------------------------------------------------------------

    assert_eq!(format!("{:?}", Punctuated::or(&[] as &[i32])), "");
    assert_eq!(format!("{:?}", Punctuated::or(&[8])), "8");
    assert_eq!(format!("{:?}", Punctuated::or(&[8, 7])), "8 or 7");
    assert_eq!(format!("{:?}", Punctuated::or(&[8, 7, 5])), "8, 7, or 5");
    assert_eq!(format!("{:?}", Punctuated::or(&[8, 7, 5, 2, 1])), "8, 7, 5, 2, or 1");

    assert_eq!(format!("{:?}", Punctuated::and(&[] as &[i32])), "");
    assert_eq!(format!("{:?}", Punctuated::and(&[8])), "8");
    assert_eq!(format!("{:?}", Punctuated::and(&[8, 7])), "8 and 7");
    assert_eq!(format!("{:?}", Punctuated::and(&[8, 7, 5])), "8, 7, and 5");
    assert_eq!(format!("{:?}", Punctuated::and(&[8, 7, 5, 2, 1])), "8, 7, 5, 2, and 1");

    assert_eq!(format!("{:?}", Punctuated::join(&[] as &[i32], ", ")), "");
    assert_eq!(format!("{:?}", Punctuated::join(&[8], ", ")), "8");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7], ", ")), "8, 7");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7, 5], ", ")), "8, 7, 5");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7, 5, 2, 1], ", ")), "8, 7, 5, 2, 1");

    assert_eq!(format!("{:?}", Punctuated::join(&[] as &[i32], ",")), "");
    assert_eq!(format!("{:?}", Punctuated::join(&[8], ",")), "8");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7], ",")), "8,7");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7, 5], ",")), "8,7,5");
    assert_eq!(format!("{:?}", Punctuated::join(&[8, 7, 5, 2, 1], ",")), "8,7,5,2,1");
}