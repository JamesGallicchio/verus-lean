/* Adapted from source/rust_verify_test/tests/seqs.rs */

use vstd::prelude::*;

verus! {
proof fn test_seq() {
    assert({
        let s1 = Seq::new(5, |i: int| 10 * i);
        let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
        let s3 = s2.subrange(1, 4);
        let s4 = Seq::<int>::empty().push(10).push(20).push(30);
        let s5 = s3.add(s1);
        let s6 = s4.map(|i: int, a: int| 2 * i + a);
        let s7 = seq![true ==> false, false ==> true]; // this is seq<bool> but Lean refuses it -- can we assume that we are in the classical setting in Lean?
        let s8: Seq<int> = seq![5; 10];

        s1.len() == 5 && s1.index(3) == 30 &&
        s1 === s2 &&
        s3.len() == 3 &&
        s3 === s4 && // changed from =~=
        s5.len() == 8 && s5.index(1) == 20 && s5.index(6) == 30 &&
        s6.len() == s4.len() && s6.index(2) == 34 &&
        !s7.index(0) && s7.index(1) &&
        s8[0] == 5 && s8.len() == 10 &&
        s1.to_set().finite() &&
        s6.to_set().finite() &&
        s7.to_set().finite()
    }) by (lean_proof as a0);
}

proof fn test1_fails1() {
    assert({
        let s1 = Seq::new(5, |i: int| 10 * i);
        s1.len() == 5 && s1.index(3) == 30 && s1.index(5) == 50 // FAILS
    }) by (lean_proof as a0);
}

proof fn test1_fails2() {
    assert({
        let s1 = Seq::new(5, |i: int| 10 * i);
        let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
        let s3 = s2.subrange(1, 4);
        let s4 = Seq::<int>::empty().push(10).push(20).push(30);
        let s5 = s3.add(s1);

        s1.len() == 5 && s1.index(3) == 30 &&
        s1 === s2 &&
        s3.len() == 3 &&
        s3 === s4 && // =~=
        s5.len() == 8 && s5.index(1) == 20 && s5.index(6) == 30 &&
        false // FAILS
    }) by (lean_proof as a0);
}


proof fn auto_extensionality_syntax1() {
    assert({
        let s1 = Seq::new(5, |i: int| 10 * i);
        let s2 = Seq::<int>::empty().push(0).push(10).push(20).push(30).push(40);
        
        s1.len() == 5 && s1.index(3) == 30 && s1 == s2
        // assert_seqs_equal!(s1, s2); // old syntax
        // assert_seqs_equal!(s1 == s2); // new syntax
    }) by (lean_proof as a0);
}

proof fn filter_lemmas() {
    assert({
        let s1 = seq![10, 20, 30, 45, 55, 70];
        let s2 = s1.filter(|x: int| x < 40);
        let s3 = seq![90, 100];
        let s4 = s3.filter(|x: int| x < 40);
        // Test for successful broadcast of filter_lemma
        forall|i: nat| i < s2.len() ==> s2[i as int] < 40 &&
        // Test for successful broadcast of filter_distributes_over_add
        (s1 + s3).filter(|x: int| x < 40) == (s2 + s4) &&
        // TODO: the following test will verify even if
        // push_distributes_over_add is not broadcasted.
        // Test for successful broadcast of push_distributes_over_add
        (s2 + s4).push(120) == s2 + s4.push(120)
    }) by (lean_proof as a0);
}

fn main() 
{}

}
