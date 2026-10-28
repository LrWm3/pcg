//! A temporary used to call `next` can die while the iterator and multiple
//! references returned from it remain live. Its post-call lifetime projection
//! must stay connected to the iterator's future projection.
struct Iter<'a> { tail: &'a mut [u32] }

impl<'a> Iter<'a> {
    fn next(&mut self) -> Option<&'a mut u32> { None }
}

fn visit(values: &mut [u32]) {
    let mut iterator = Iter { tail: values };
    let first = iterator.next();
    let second = iterator.next();
    if let (Some(first), Some(second)) = (first, second) {
        *first = 7;
        *second = 8;
    }
    drop(iterator);
    // PCG: bb1[0] post_main: _5 before bb0[9]:PostOperands↓'?21 after bb0 -> iterator↓'?17
    // ~PCG: bb1[0] pre_main: Unlabel lifetime projection (exact _5 && in_source_nodes && edge_type(BorrowFlow { future_edge_kind: Some(FromExpansion) }))
}

fn main() { let mut values = [1, 2]; visit(&mut values); }
