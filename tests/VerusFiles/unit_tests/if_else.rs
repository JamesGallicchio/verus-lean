// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A4 "`if` / `else`" (all green).
// Demonstrates: `if`/`else` in both spec position (expression) and exec
// position (statement) lower faithfully.
use vstd::prelude::*;

verus! {

spec fn max(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

proof fn spec_if() {
    assert(max(3, 5) == 5);
    assert(max(9, 2) == 9);
    assert(max(4, 4) == 4);
}

fn exec_if(x: u32) -> (r: u32)
    ensures r >= x, r >= 10,
{
    if x < 10 { 10 } else { x }
}

fn main() {}

} // verus!
