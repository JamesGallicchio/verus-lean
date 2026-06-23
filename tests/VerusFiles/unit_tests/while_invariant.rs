// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A4 "`while` loops + invariants" (all green).
// Demonstrates: a `while` loop with an `invariant` (and a `decreases` measure)
// verifies its post-condition end-to-end.
use vstd::prelude::*;

verus! {

fn count_to(n: u32) -> (r: u32)
    requires n <= 1000,
    ensures r == n,
{
    let mut i: u32 = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    {
        i = i + 1;
    }
    i
}

fn main() {}

} // verus!
