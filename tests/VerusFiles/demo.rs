use vstd::prelude::*;
fn main() {}

verus! {

fn find_max(v: Vec<u64>) -> (result: u64)
    requires
        v@.len() > 0,
    ensures
        exists|i: int| 0 <= i && i < v@.len() && result == v@[i],
        forall|i: int| 0 <= i && i < v@.len() ==> result >= v@[i],
{
    let mut max = v[0];
    for i in 1..v.len()
        invariant
            1 <= i <= v@.len(),
            exists|j: int| 0 <= j && j < i && max == v@[j],
            forall|j: int| 0 <= j && j < i ==> max >= v@[j],
            v@.len() > 0,
        decreases v@.len() - i,
    {
        if v[i] > max {
            max = v[i];
        }
    }
    max
}

} // verus!
