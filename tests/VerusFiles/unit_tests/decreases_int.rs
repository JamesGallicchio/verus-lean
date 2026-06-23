// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B5 "`decreases` - function (int-valued termination)"
// ([CORE-decreases], all green; verified 2026-06-22).
// Demonstrates: a recursive spec function with an int-valued `decreases abs(i)`
// measure emits `rec function ... decreases abs(i)` and passes Strata's
// int-termination check (non-negativity + strict decrease on every call edge:
// i-1 for i>0, i+1 for i<0).
//
// NOTE: this row is about *termination*, not about proving *properties* of the
// function. An int-recursive spec fn is a pure UF with no definitional axiom in
// Strata, so e.g. `assert(walk(0) == 0)` comes back cvc5-unknown (the §A5 / §B5
// pure-UF limitation). The anchor below therefore asserts a property of the
// *non-recursive* `abs`, and merely *references* `walk` to emit its termination
// obligations.
use vstd::prelude::*;

verus! {

spec fn abs(i: int) -> int {
    if i < 0 { -i } else { i }
}

spec fn walk(i: int) -> int
    decreases abs(i),
{
    if i == 0 {
        0
    } else if i > 0 {
        walk(i - 1)
    } else {
        walk(i + 1)
    }
}

proof fn termination_anchor() {
    assert(abs(-5) == 5); // provable: `abs` is non-recursive
    let _g = walk(3);     // reference `walk` -> emits its termination obligations
}

fn main() {}

} // verus!
