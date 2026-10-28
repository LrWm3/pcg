//! A reference stored through an argument remains observable by the caller
//! after the last executable read of that argument.
fn visit<'a>(values: &mut [&'a mut u32], index: usize, replacement: &'a mut u32) {
    *replacement = 9;
    values[index] = replacement;
    let _actual = *values[index];
    // PCG: bb2[5] pre_main: borrow: _4 before bb1[0]:PostOperands = &mut  *replacement
}

fn main() {
    let (mut old, mut new) = (1, 2);
    let mut values = [&mut old];
    visit(&mut values, 0, &mut new);
    assert_eq!(*values[0], 9);
}
