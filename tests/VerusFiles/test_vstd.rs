use vstd::prelude::*;

verus! {
proof fn test_seq1() {
    assert({
        let s: Seq<int> = seq![0, 10, 20, 30, 40]; // directly into Lean syntax (current approach), or push recursively
        s.len() == 5 && s[2] == 20 && s[3] == 30
    }) by (lean_proof as a0);
}

proof fn test_set1() {
    assert({
        let s: Set<int> = set![0, 10, 20, 30, 40];
        s.finite() && s.contains(20) && s.contains(30) && !s.contains(60)
    }) by (lean_proof as a1);
}

proof fn test_map1() {
    assert({
        let m: Map<int, int> = map![0 => 0, 10 => 100, 20 => 200, 30 => 300, 40 => 400];
        m.dom().contains(20) && m.dom().contains(30) && !m.dom().contains(60) &&
        m[20] == 200 && m[30] == 300
    }) by (lean_proof as a2);
}

proof fn test_set2() {
    assert({
        let s: Set<int> = Set::new(|i: int| 0 <= i <= 40 && i % 10 == 0);
        s.contains(20) && s.contains(30) && !s.contains(60)
    }) by (lean_proof as a3);
}

proof fn test_set3() {
    assert({
        let s_infinite: Set<int> = Set::new(|i: int| i % 10 == 0);
        s_infinite.contains(20) && s_infinite.contains(30) && !s_infinite.contains(35)
    }) by (lean_proof as a4);
}

proof fn test_map2() {
    assert({
        let m: Map<int, int> = Map::new(|i: int| 0 <= i <= 40 && i % 10 == 0, |i: int| 10 * i);
        m[20] == 200 && m[30] == 300
    }) by (lean_proof as a5);
}

proof fn test_map3() {
    assert({
        let m_infinite: Map<int, int> = Map::new(|i: int| i % 10 == 0, |i: int| 10 * i);
        m_infinite[20] == 200 && m_infinite[30] == 300 && m_infinite[90] == 900
    }) by (lean_proof as a6);
}

proof fn test_seq2() {
    assert({
        let s1: Seq<int> = seq![0, 10, 20, 30, 40];
        let s2: Seq<int> = seq![0, 10] + seq![20] + seq![30, 40];
        let s3: Seq<int> = Seq::new(5, |i: int| 10 * i);
        s1 === s2 && s1 === s3
    }) by (lean_proof as a7);
}

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>) by (lean)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{}

fn main() 
{}

}
