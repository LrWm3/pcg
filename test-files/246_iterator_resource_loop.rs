//! Loop restoration must join the iterator's storage and element resources.

fn visit(values: &mut [&mut u32]) {
    let mut it = values.iter_mut();
    loop {
        match it.next() {
            Some(value) => **value = 7,
            None => break,
        }
    }
    drop(it);
    if !values.is_empty() {
        assert_eq!(*values[0], 7);
    }
}

fn main() {
    visit(&mut []);
    let (mut first, mut second) = (1, 2);
    visit(&mut [&mut first, &mut second]);
    assert_eq!((first, second), (7, 7));
}
