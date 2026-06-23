// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B2 "`int` (mathematical)" (all green).
// Demonstrates: the ghost `int` type is infinite-precision — products that
// would overflow any fixed width stay exact, and ordering is unbounded.
use vstd::prelude::*;

verus! {

proof fn infinite_precision() {
    let x: int = 1_000_000_000_000;
    assert(x * x == 1_000_000_000_000_000_000_000_000); // no wrap at any fixed width
    assert(x + 1 > x);                                  // unbounded above
    assert(x - 2 * x == -x);                            // exact signed arithmetic
}

fn main() {}

} // verus!
