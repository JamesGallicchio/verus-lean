// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B4 "`calc!` proofs" (all green).
// Demonstrates: a `calc!` chain lowers to an explicit chain of assertions; the
// step relations compose to the overall relation.
use vstd::calc_macro::*;
use vstd::prelude::*;

verus! {

proof fn calc_chain() {
    let a: int = 2;
    calc! {
        (<=)
        a; {}
        a + 3; {}
        5;
    }
}

fn main() {}

} // verus!
