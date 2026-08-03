// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// Demonstrates the Vec operations that share a name shape with the residual
// `Vec_*` drop rule and therefore must be lowered before it:
//   * `Vec::new()` / `Vec::with_capacity(n)` -> `Sequence.empty`
//   * `let n = v.len()` as an assignment's entire RHS -> `Sequence.length(v)`
//   * `push` through a `&mut` parameter reborrow -> `Sequence.build`
use vstd::prelude::*;

verus! {

// `Vec::new()` is a compiler intrinsic with no exported declaration; the empty
// vector must still constrain the binding's length.
fn new_is_empty() {
    let v: Vec<i64> = Vec::new();
    assert(v.len() == 0);
}

// Element types without a dedicated empty-sequence token use the annotated
// `Sequence.empty<T>()` fallback.
fn tuple_new_is_empty() {
    let v: Vec<(i64, i64)> = Vec::new();
    assert(v.len() == 0);
}

// `with_capacity` also yields an empty vector: the capacity hint is not a length.
fn with_capacity_is_empty() {
    let v: Vec<i64> = Vec::with_capacity(8);
    assert(v.len() == 0);
}

// `.len()` as the whole right-hand side of a `let`: the binding must carry the
// sequence's length, not an arbitrary value.
fn len_binding(v: Vec<i64>) {
    let n: usize = v.len();
    assert(n == v.len());
}

// Push through a `&mut` parameter, whose reborrow puts `MutRefCurrent` on both
// sides of the prophecy equality.
fn push_through_mut_param(v: &mut Vec<i64>, x: i64)
    ensures
        v.len() == old(v).len() + 1,
{
    v.push(x);
}

// The three operations combined: build a vector from empty and relate its
// length to the number of pushes.
fn new_then_push(x: i64, y: i64) -> (out: Vec<i64>)
    ensures
        out.len() == 2,
        out[0] == x,
{
    let mut out: Vec<i64> = Vec::new();
    out.push(x);
    out.push(y);
    out
}

fn main() {}

} // verus!
