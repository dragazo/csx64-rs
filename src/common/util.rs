/// Gets two mutable references to distinct elements of a slice. Panics if `a == b`.
pub(crate) fn mut2<T>(src: &mut [T], a: usize, b: usize) -> (&mut T, &mut T) {
    assert_ne!(a, b);
    if a < b {
        let (x, y) = src.split_at_mut(b);
        (&mut x[a], &mut y[0])
    }
    else {
        let (y, x) = src.split_at_mut(a);
        (&mut x[0], &mut y[b])
    }
}
#[test]
fn test_mut2() {
    let mut v: Vec<usize> = vec![0, 1, 2, 3, 4, 5];
    for a in 0..v.len() {
        for b in 0..v.len() {
            if a == b { continue; }

            let (x, y) = mut2(&mut v, a, b);
            assert_eq!(*x, a);
            assert_eq!(*y, b);
        }
    }
}