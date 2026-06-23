// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A4 "Early `return`" (#871, all green).
// Demonstrates: an early `return` lowers to a native Boole `exit <proc>;`, and
// the post-condition holds on both the early and the fall-through path.
use vstd::prelude::*;

verus! {

fn clamp10(x: u32) -> (r: u32)
    ensures
        r <= 10,
        x <= 10 ==> r == x,
{
    if x > 10 {
        return 10; // early exit
    }
    x
}

fn main() {}

} // verus!
