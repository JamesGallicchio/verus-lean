use vstd::prelude::*;

verus! {

spec fn abs(i: int) -> int {
    if i < 0 {
        -i
    } else {
        i
    }
}

spec fn is_even(i: int) -> bool
    decreases abs(i),
{
    if i == 0 {
        true
    } else if i > 0 {
        is_odd(i - 1)
    } else {
        is_odd(i + 1)
    }
}

spec fn is_odd(i: int) -> bool
    decreases abs(i),
{
    if i == 0 {
        false
    } else if i > 0 {
        is_even(i - 1)
    } else {
        is_even(i + 1)
    }
}

proof fn even_odd_mod2(i: int) by (lean)
    ensures
        is_even(i) <==> i % 2 == 0,
        is_odd(i) <==> i % 2 == 1,
    decreases abs(i),
{ }

fn main()
{}

}
