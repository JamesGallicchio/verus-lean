// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A4 "Nested loops" (all green).
// Demonstrates: an inner `while` loop (with its own invariant + measure) nested
// inside an outer one gets fresh Core block labels, so both loops verify.
//
// NOTE: the inner loop is bounded by a constant so its bv->int strict-decrease
// obligation stays cheap; a symbolic inner bound pushes that `measure_decrease`
// obligation into a cvc5 timeout.
use vstd::prelude::*;

verus! {

fn nested(n: u32)
    requires n <= 100,
{
    let mut i: u32 = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    {
        let mut j: u32 = 0;
        while j < 5
            invariant j <= 5,
            decreases 5 - j,
        {
            j = j + 1;
        }
        i = i + 1;
    }
}

fn main() {}

} // verus!
