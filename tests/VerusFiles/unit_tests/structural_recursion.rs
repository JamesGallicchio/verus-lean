// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md rows:
//   A5 "Structural recursion (over datatypes)" (claimed all green)
//   B5 "decreases - function (structural @[cases])" (claimed all green)
// Demonstrates: a spec function recursing over a recursive datatype with a
// `decreases <datatype>` measure (the measure decreases structurally to a
// field). `int` return is used to stay off the abstract-`nat` path.
//
// STATUS: verifies end-to-end. The translator recognizes the datatype-valued
// `decreases` parameter and emits Strata's `@[cases]` structural-recursion
// marker on the corresponding `rec function` binding, so Strata uses its
// structural `adtRank` termination path. Recursion over a datatype with an
// *int* measure (e.g. `decreases n`) remains covered by decreases_int.rs.
use vstd::prelude::*;

verus! {

enum List {
    Nil,
    Cons(u32, Box<List>),
}

spec fn len(l: List) -> int
    decreases l,
{
    match l {
        List::Nil => 0,
        List::Cons(_, tl) => 1 + len(*tl),
    }
}

proof fn structural_smoke() {
    assert(len(List::Nil) == 0);
    let xs = List::Cons(7, Box::new(List::Nil));
    assert(len(xs) == 1);
}

fn main() {}

} // verus!
