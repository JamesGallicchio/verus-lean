// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A3 "References (`&` / `&mut`)" (all green).
// Demonstrates: shared and mutable references erase to plain values
// (verification-equivalent); `&mut` state is tracked via `final(...)`/`old(...)`.
use vstd::prelude::*;

verus! {

// Shared reference: read-through.
fn read_ref(x: &u32) -> (r: u32)
    ensures r == *x,
{ *x }

// Mutable reference: the post-state relates to the pre-state via `final`/`old`.
fn bump(x: &mut u32)
    requires *old(x) < 100,
    ensures *final(x) == *old(x) + 1,
{ *x = *x + 1; }

fn main() {}

} // verus!
