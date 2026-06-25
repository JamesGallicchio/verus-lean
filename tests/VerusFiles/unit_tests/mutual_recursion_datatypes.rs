// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A5 "Mutual recursion (over datatypes)" (#599, claimed all green).
// Demonstrates: two spec functions that mutually recurse over a pair of
// mutually-recursive datatypes (Tree / Forest), each with a structural
// `decreases` on its datatype argument.
//
// STATUS: verifies end-to-end (13/13). Verus groups the mutually-recursive
// `Tree`/`Forest` datatypes into one `mutualBlock`; the translator emits them as
// a single `command_datatypes` block, so they reference each other under Strata's
// two-phase name pre-registration. Both datatype-measured recursive functions
// emit `@[cases]` on their decreasing parameter for structural termination.
use vstd::prelude::*;

verus! {

enum Tree {
    Leaf(u32),
    Branch(Box<Forest>),
}

enum Forest {
    Empty,
    Grove(Box<Tree>, Box<Forest>),
}

spec fn tree_size(t: Tree) -> int
    decreases t,
{
    match t {
        Tree::Leaf(_) => 1,
        Tree::Branch(f) => forest_size(*f),
    }
}

spec fn forest_size(f: Forest) -> int
    decreases f,
{
    match f {
        Forest::Empty => 0,
        Forest::Grove(t, rest) => tree_size(*t) + forest_size(*rest),
    }
}

proof fn mutual_smoke() {
    assert(tree_size(Tree::Leaf(9)) == 1);
    assert(forest_size(Forest::Empty) == 0);
}

fn main() {}

} // verus!
