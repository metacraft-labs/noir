// Regression fixture for a silent tracer defect.
//
// `DebugInstrumenter::walk_statement` used to end in a `_ => {}` catch-all.
// `StatementKind::{Loop, While}` fell into it, so assignments inside a `while`
// or `loop` body were never instrumented: this program recorded `acc = 0` and
// `i = 0` once and then never again, while the circuit correctly computed 10.
// The trace was wrong and every test still passed.
//
// `tooling/tracer/tests/test_tracer.rs::test_while_loop_body_assignments_are_recorded`
// pins the recorded value sequence. Keep both.
unconstrained fn main(n: u32, out: u32) {
    let mut acc: u32 = 0;
    let mut i: u32 = 0;
    while i < n {
        acc = acc + i;
        i = i + 1;
    }
    assert(acc == out);
}
