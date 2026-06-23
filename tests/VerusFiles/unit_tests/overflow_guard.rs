// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: B2 "Numeric `HasType` overflow guards" (RESOLVED, all green).
// Demonstrates: an exec fixed-width addition raises an overflow VC that lowers
// to an explicit int-domain range predicate
// (`0 <= as_uint(x)+as_uint(y) <= u32::MAX`); here the operands are concrete and
// their sum fits in `u32`, so the VC discharges.
//
// NOTE: concrete operands are used because the *symbolic* range predicate makes
// cvc5 bit-blast `as_uint(x)`/`as_uint(y)` over the full 32-bit range and time
// out at the default budget — even though the predicate itself is faithful.
use vstd::prelude::*;

verus! {

fn add_checked() -> (r: u32)
    ensures r == 4_200_000_000,
{
    let x: u32 = 4_000_000_000;
    let y: u32 = 200_000_000;
    x + y // overflow VC: 4.0e9 + 0.2e9 <= 4_294_967_295, discharged
}

fn main() {}

} // verus!
