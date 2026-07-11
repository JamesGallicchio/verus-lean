use vstd::prelude::*;
verus! {

// Regression coverage for the signed division/remainder lowering.
//
// Rust's exec signed `/` and `%` are exported as `core::ops::arith::{Div,Rem}`
// trait calls; the parser rewrites them to native `TruncDiv`/`TruncRem`
// (truncate toward zero; the remainder takes the sign of the dividend), which
// lower to Boole `sdiv`/`smod` (SMT `bvsdiv`/`bvsrem`). The `0 <= a`
// preconditions keep those run-time results equal to the Euclidean spec
// `/`/`%`.
//
// The remainder cases assert exact equality with the spec `%` (which also
// lowers to `smod`, so the obligation is reflexive). The division case asserts
// bitvector bounds rather than `res == a / b`: the spec `/` is modeled in the
// integer domain (`as_sint(a) div as_sint(b)`), so an exact comparison against
// the bitvector `sdiv` body is a hard mixed int/bv obligation independent of
// this rewrite. Signed `%` with a negative dividend — where exec and spec truly
// diverge — is documented by StrataBooleTest/smod_truncated_not_euclidean.lean
// and is not exercisable here because Verus rejects the unconstrained program.

// signed remainder, statement position, i64
fn rem_i64(a: i64, b: i64) -> (res: i64)
    requires 0 < b, 0 <= a,
    ensures res == a % b,
{
    a % b
}

// signed remainder at a narrower width (bv32)
fn rem_i32(a: i32, b: i32) -> (res: i32)
    requires 0 < b, 0 <= a,
    ensures res == a % b,
{
    a % b
}

// signed division: the rewrite produces `sdiv`; assert bitvector bounds
fn div_i64(a: i64, b: i64) -> (res: i64)
    requires 0 < b, 0 <= a,
    ensures 0 <= res, res <= a,
{
    a / b
}

fn main() {}

}
