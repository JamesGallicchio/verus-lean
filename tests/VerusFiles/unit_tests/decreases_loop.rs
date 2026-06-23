// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B5 "`decreases` - loop-level" ([CORE-decreases], all green).
// Demonstrates: a loop carries a native `while ... decreases ...` measure, and
// Strata enforces the non-negativity + strict-decrease obligations.
//
// NOTE: the measure is `n - i` over a *bounded* counter (`n <= 1000`). cvc5
// discharges the bv->int strict-decrease obligation under that bound; an
// unbounded `decreases i` countdown instead times out on the same bridge.
use vstd::prelude::*;

verus! {

fn loop_with_measure(n: u32)
    requires n <= 1000,
{
    let mut i: u32 = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
}

fn main() {}

} // verus!
