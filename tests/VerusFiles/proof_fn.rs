#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn p(u: usize) -> bool {
    u >> 8 == 0
}

proof fn range_property(u: usize) by(lean)
    requires 25 <= u < 100,
    ensures p(u),
{}

pub closed spec fn min(x: int, y: int) -> int {
    if x <= y {
        x
    } else {
        y
    }
}

pub proof fn lemma_min(x: int, y: int) by(lean)
    ensures
        min(x, y) <= x,
        min(x, y) <= y,
        min(x, y) == x || min(x, y) == y,
{
}

fn main() {
}

} // verus!
