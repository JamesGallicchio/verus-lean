// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B1 "`#[verifier::external]`" (all green).
// Demonstrates: an `#[verifier::external]` item is invisible to Verus (dropped
// from translation entirely), even when its body uses unsupported features
// (here `f64`), while the rest of the module still verifies.
use vstd::prelude::*;

verus! {

// Not seen by Verus at all — `f64` would otherwise be unsupported.
#[verifier::external]
fn uses_float() -> f64 {
    3.14
}

proof fn still_verifies() {
    assert(1 + 1 == 2);
}

fn main() {}

} // verus!
