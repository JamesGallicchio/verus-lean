use vstd::prelude::*;

verus! {

#[verifier::opaque]
spec fn secret(x: int, y: int) -> int {
    x + y
}

// Without reveal: can only use `secret` as an uninterpreted function.
proof fn test_opaque()
{
    assert(secret(10, 20) == secret(10, 20));
}

// With reveal: the body becomes visible.
proof fn test_reveal()
{
    reveal(secret);
    assert(secret(3, 4) == 7);
}

fn main()
{}

}
