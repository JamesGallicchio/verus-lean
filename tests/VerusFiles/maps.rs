/* Adapted from source/rust_verify_test/tests/maps.rs */

use vstd::prelude::*;
// use vstd::set::*;
// use vstd::map::*;

verus! {

proof fn test_map() {
    assert({
        let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
        let m1 = s1.mk_map(|k: int| 10 * k);
        let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
        let m2 = s2.mk_map(|k: int| 3 * k + 7 * k);
        let m3 = map![10int => true ==> false, 20int => false ==> true];
        let m4 = map![10int => true ==> false, 20int => false ==> true,];

        m1.index(2) == 20 && m1 === m2 && // Verus-lean does not yet support extensional equality =~=
        !m3.index(10) && m3.index(20) && 
        !m4.index(10) && m4.index(20)
    }) by (lean_proof as a0);
}

proof fn testfun_eq() {
    assert({
        // let s = Set::<int>::empty().insert(1).insert(2).insert(3);
        let s = Set::<int>::empty();
        // let m1 = s.mk_map(|x: int| x + 4);
        let m2 = s.mk_map(|y: int| y + (2 + 2));
        // m1 and m2 are equal even without extensional equality:
        equal(m2, m2)
    }) by (lean_proof as a0);
}

proof fn test1_fails1() {
    assert({
        let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
        let m1 = s1.mk_map(|k: int| 10 * k);
        let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
        let m2 = s2.mk_map(|k: int| 3 * k + 7 * k);

        m1.index(2) == 20 && m1.index(4) == 40 && m1 === m2 // Verus-lean: changed =~= to ===
    }) by (lean_proof as a0);
}

proof fn test1_fails2() {
    assert({
        let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
        let m1 = s1.mk_map(|k: int| 10 * k);
        let s2 = Set::<int>::empty().insert(1).insert(3).insert(2);
        let m2 = s2.mk_map(|k: int| 3 * k + 8 * k);
        m1.index(2) == 20 && equal(m1, m2)
    }) by (lean_proof as a0);
}

/* proof fn test1_fails_subtype() {
    assert({
        let s1 = Set::<int>::empty().insert(1).insert(2).insert(3);
        let m1 = s1.mk_map(|k: int| 10 * k);
        let m3: Map<int, int> = m1;
        let m4: Map<nat, int> = m1; // FAILS: see https://github.com/FStarLang/FStar/issues/1542
    }) by (lean_proof as a0); 
} */

proof fn test1_fails_eq() {
    assert({
        let s = Set::<int>::empty().insert(1).insert(2).insert(3);
        let m1 = s.mk_map(|x: int| x + 4);
        let m2 = s.mk_map(|y: int| (2 + 2) + y);
        // would require extensional equality:
        m1 === m2 // FAILS
    }) by (lean_proof as a0); 
}

proof fn map_contains() {
    assert({
        let m = map![10int => 100int, 20int => 200int];
        m.contains_key(10) && m.contains_value(100)
    }) by (lean_proof as a0); 
}

proof fn choose_contains_set(m: Set<nat>) by (lean)
    requires m.finite(), m.len() > 0
    ensures m.contains(m.choose())
{
}


fn main() 
{}

}
