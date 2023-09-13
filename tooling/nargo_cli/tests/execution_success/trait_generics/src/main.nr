trait Inc<X> {
    fn inc(self, t: X) -> X {
        t
    }
}

fn foo<T, A1, A2>(t: T, a1: A1, a2: A2) -> A1 where T: Inc<A1> + Inc<A2>
{
    // We know of two overloads for t.inc - from the Inc<A1> and Inc<A2> implementations
    // if this typechecks properly, we've correctly resolved them based on the arguments
    let b1: A1 = t.inc(a1);
    let b2: A2 = t.inc(a2);
    b1
}

fn bar<T, A1, A2>(t: T, a1: A1, a2: A2) -> A2 where T: Inc<A1> + Inc<A2>
{
    let b1: A1 = t.inc(a1);
    let b2: A2 = t.inc(a2);
    b2
}

fn main() {
}