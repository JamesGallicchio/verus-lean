// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B1 "`requires` / `ensures` contracts" (all green).
// Demonstrates: a precondition is assumed on entry and a postcondition is
// proved on exit; a caller must establish the callee's `requires`.
//
// NOTE: the contract is phrased over (unsigned) comparisons rather than an
// arithmetic-equality `ensures`, which would force the cvc5-hard bv->int bridge.
use vstd::prelude::*;

verus! {

fn at_least_five(x: u32) -> (r: u32)
    requires x >= 5,
    ensures r >= 5,
{
    x
}

fn caller() {
    let v = at_least_five(7); // caller discharges `7 >= 5`
    assert(v >= 5);           // relies on the callee's `ensures`
}

fn main() {}

} // verus!
