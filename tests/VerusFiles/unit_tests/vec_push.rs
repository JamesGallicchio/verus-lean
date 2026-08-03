// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// Demonstrates: executable `Vec::push` lowers to
// `out := Sequence.build(out, value)` and preserves Verus's sequence-view
// append contract.
use vstd::prelude::*;
use vstd::std_specs::vec::*;

verus! {

fn push_once(input: Vec<u32>, value: u32) -> (out: Vec<u32>)
    ensures out@ == input@.push(value),
{
    let mut out = input;
    out.push(value);

    assert(out@ == input@.push(value));
    out
}

fn push_through_mut_param(v: &mut Vec<u32>, value: u32)
    ensures final(v)@ == old(v)@.push(value),
{
    v.push(value);
}

fn main() {}

} // verus!
