use vstd::prelude::*;

verus! {

enum NatList {
    Nil,
    Cons(nat, Box<NatList>),
}

spec fn len(list: NatList) -> nat
    decreases list,
{
    match list {
        NatList::Nil => 0,
        NatList::Cons(_, tl) => 1 + len(*tl),
    }
}

proof fn rec_adt_structural_smoke() {
    let xs = NatList::Cons(3nat, Box::new(NatList::Nil));
    assert(len(NatList::Nil) == 0);
    assert(len(xs) == 1);
}

fn main() {}

} // verus!
