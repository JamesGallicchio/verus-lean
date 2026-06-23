// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A4 "`let` / `let mut` bindings" (all green).
// Demonstrates: both `let` and `let mut` collapse to a mutable Boole `var`;
// reassignment of a `let mut` binding is tracked.
use vstd::prelude::*;

verus! {

proof fn let_and_let_mut() {
    let x: int = 3;       // immutable binding
    let mut y: int = x + 1; // mutable binding
    y = y * 2;
    assert(x == 3);
    assert(y == 8);
}

fn main() {}

} // verus!
