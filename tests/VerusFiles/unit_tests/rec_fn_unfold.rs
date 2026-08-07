// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B5 "`decreases` - function (int-valued termination)".
// Demonstrates: a recursive spec function measured by an int carries a defining
// axiom in the Boole output, so a caller can evaluate it at a concrete argument.
//
// Strata writes definitional axioms only for functions that recurse structurally
// on a datatype (`@[cases]`); a function measured by an int is encoded as an
// uninterpreted function. The translator supplies the defining axiom for those,
// which is what makes the assertion below provable. Turning the aid off with
// `--synth-disable recFnUnfold` leaves `walk` uninterpreted and the assertion
// comes back solver-unknown, so this test distinguishes the two encodings.
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

proof fn unfold_anchor() {
    assert(walk(0) == 0); // needs `walk`'s defining axiom at i == 0
}

fn main() {}

} // verus!
