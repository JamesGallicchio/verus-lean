// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md rows:
//   A5 "Structural recursion (over datatypes)" (claimed all green)
//   B5 "decreases - function (structural @[cases])" (claimed all green)
// Demonstrates: a spec function recursing over a recursive datatype with a
// `decreases <datatype>` measure (the measure decreases structurally to a
// field). `int` return is used to stay off the abstract-`nat` path.
//
// STATUS (does NOT currently verify — matrix over-claims these rows):
// Strata Core rejects the emitted bare `rec function len ... decreases l` with
//   "recursive function 'len': structural recursion requires @[cases]".
// The translator threads a datatype `decreases` but does not emit Strata's
// `@[cases]` structural-recursion marker, so datatype-measured recursion fails
// at Core. This matches the differential_status.md `[CORE-decreases]` note
// (the int-measured path was fixed 2026-06-22, but the *structural* path was
// not). Recursion over a datatype with an *int* measure (e.g. `decreases n`)
// does verify — see decreases_int.rs.
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
