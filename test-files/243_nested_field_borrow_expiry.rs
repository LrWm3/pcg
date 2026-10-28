//! The outer reference's lifetime projection can become dead while a field
//! reborrow still uses its expanded referent. Restore the source only after
//! that structural expansion has been packed.
fn visit(values: &mut [Option<&mut u32>]) {
    if let Some(value) = &mut values[0] {
        // PCG: bb3[2] pre_main: borrow: _2 <before bb1[2]:PreOperands> = &mut  (*values)[_3] under conditions bb1 -> bb2
        // ~PCG: bb3[2] pre_operands: Remove Edge borrow: _2 <before bb1[2]:PreOperands> = &mut  (*values)[_3] under conditions bb1 -> bb2
        **value = 7;
    }
}

fn main() {
    let mut value = 1;
    visit(&mut [Some(&mut value)]);
    assert_eq!(value, 7);
}
