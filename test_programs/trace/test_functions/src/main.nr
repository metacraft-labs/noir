fn main(x: Field, y: pub Field) {
    assert(add_one(x) == y);
}

fn add_one(v: Field) -> Field {
    v + 1
}

#[test]
fn test_passes() {
    let r = add_one(2);
    assert(r == 3);
}

#[test]
fn test_fails() {
    let r = add_one(2);
    assert(r == 4);
}

#[test(should_fail)]
fn test_should_fail() {
    let r = add_one(2);
    assert(r == 5);
}

mod tests {
    use crate::add_one;

    #[test]
    fn test_nested() {
        let r = add_one(10);
        assert(r == 11);
    }
}
