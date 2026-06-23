// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B1 "`spec` / `proof` / `exec` modes" (all green).
// Demonstrates: a `spec` function (-> Boole `function`), a `proof` lemma, and an
// `exec` function (-> Boole `procedure`) interoperate end-to-end.
use vstd::prelude::*;

verus! {

spec fn double(x: int) -> int { x * 2 } // spec mode -> Boole function

proof fn double_is_sum(x: int) // proof mode -> spec-only procedure
    ensures double(x) == x + x,
{ }

fn compute_double(x: u32) -> (r: u32) // exec mode -> Boole procedure
    requires x == 21, // pinned so the result is concrete (avoids the bv->int bridge)
    ensures r as int == double(x as int),
{ x + x }

fn main() {}

} // verus!
