trait Asd {
    fn asd(self) -> Field;
}

struct Add10  { x: Field, }
struct Add20  { x: Field, }
struct Add30  { x: Field, }
struct AddXY  { x: Field, y: Field, }

impl Asd for Add10 { fn asd(self) -> Field { self.x + 10 } }
impl Asd for Add20 { fn asd(self) -> Field { self.x + 20 } }
impl Asd for Add30 { fn asd(self) -> Field { self.x + 30 } }

impl Asd for AddXY {
    fn asd(self) -> Field {
        self.x + self.y
    }
}

fn assert_asd_eq_100<T>(t: T) where T: Asd {
    assert(t.asd() == 100);
}

fn main() {
    let x  = Add10{ x: 90 };
    let z  = Add20{ x: 80 };
    let a  = Add30{ x: 70 };
    let xy = AddXY{ x: 30, y: 70 };

    assert_asd_eq_100(x);
    assert_asd_eq_100(z);
    assert_asd_eq_100(a);
    assert_asd_eq_100(xy);
}
