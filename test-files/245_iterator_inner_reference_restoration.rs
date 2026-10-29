//! Returned iterator elements expire before the original slice is read.
//! The constructor's retained inner projection must not hold its own owner
//! behind a future projection after the iterator and both yields have died.

fn visit(values: &mut [&mut u32]) {
    // PCG: bb8[6] pre_operands: Remove Edge call core::slice::<impl [T]>::iter_mut at bb0[3]: [_3 before bb0[3]:PostOperands↓'?33 before bb0[3]:PostMain, _3 before bb0[3]:PostOperands↓'?34 before bb0[3]:PostMain] -> [it before bb3[4]:PostOperands↓'?31 before bb1[4]:PostMain, it before bb3[4]:PostOperands↓'?32 before bb1[4]:PostMain] under conditions bb4 -> bb6, bb6 -> bb7
    // PCG: bb0[3] post_main: call core::slice::<impl [T]>::iter_mut at bb0[3]: [_3 before bb0[3]:PostOperands↓'?33 before bb0[3]:PostMain, _3 before bb0[3]:PostOperands↓'?34 before bb0[3]:PostMain] -> [it↓'?31, it↓'?32]
    let mut it = values.iter_mut();
    let first = it.next();
    let second = it.next();
    drop(it);
    match (first, second) {
        (Some(first), Some(second)) => {
            **first = 7;
            **second = 8;
        }
        _ => {
            assert!(false);
        }
    }
    let first = *values[0];
    let second = *values[1];
    assert!(first == 7);
    assert!(second == 8);
}

fn main() {
    let (mut first, mut second) = (1, 2);
    visit(&mut [&mut first, &mut second]);
    assert_eq!((first, second), (7, 8));
}
