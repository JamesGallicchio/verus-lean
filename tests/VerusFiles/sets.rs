/* Adapted from source/rust_verify_test/tests/sets.rs */

use vstd::prelude::*;
// use vstd::set::*;

verus! {

proof fn test_len<A>(s: Set<A>) {
    assert(s.len() as int >= 0) by (lean_proof as a0);
}

proof fn test_len_fails<A>(s1: Set<A>, s2: Set<A>) {
    assert(s1.len() == s2.len()) by (lean_proof as a0); // FAILS
}

proof fn test_set()
{
    assert({
        let nonneg = Set::new(|i: int| i >= 0);
        let pos1 = nonneg.filter(|i: int| i > 0);
        let pos2 = nonneg.map(|i: int| i + 1);
        forall|i: int| nonneg.contains(i) == (i >= 0) &&
        forall|i: int| pos1.contains(i) == (i > 0) &&
        forall|i: int| pos2.contains(i) == (i > 0) &&
        pos1 === pos2
    }) by (lean_proof as a0);
}

spec fn set_map<A>(s: Set<A>, f: spec_fn(A) -> A) -> Set<A> {
    Set::new(|a: A| exists|x: A| s.contains(x) && a === f(x))
}

proof fn test_set_fails() {
    assert({
        let nonneg = Set::new(|i: int| i >= 0);
        let pos1 = nonneg.filter(|i: int| i > 0);
        let pos2 = set_map(nonneg, |i: int| i + 1);
        forall|i: int| nonneg.contains(i) == (i >= 0) &&
        forall|i: int| pos1.contains(i) == (i > 0) &&
        forall|i: int| pos2.contains(i) == (i > 0) &&
        pos1 === pos2
    }) by (lean_proof as a0);
}

spec fn f(x: int) -> bool {
    true
}

proof fn test_witness() {
    assert({
        let s = Set::new(|x: int| f(x));
        exists|x: int| f(x) && s.contains(x) && s.contains(s.choose())
    }) by (lean_proof as a0);
}

proof fn test_choose_fails_witness() {
    assert({
        let s = Set::new(|x: int| f(x));
        s.contains(s.choose()) // FAILS if not by Lean
    }) by (lean_proof as a0);
}

proof fn test_set_fold() {
    assert({
        let s: Set<nat> = set![9];
        s.finite() && s.len() > 0 &&
        s.fold(0, |p: nat, a: nat| p + a) == 9 &&
        set![].fold(0, |p: nat, a: nat| p + a) == 0
    }) by (lean_proof as a0);
}

fn main() 
{}

}
