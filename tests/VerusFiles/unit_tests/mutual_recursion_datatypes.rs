// UNIT TEST — authored for verus-boogie; NOT adopted from the Verus repo.
// FEATURE_SUPPORT_MATRIX.md row: A5 "Mutual recursion (over datatypes)" (#599, claimed all green).
// Demonstrates: two spec functions that mutually recurse over a pair of
// mutually-recursive datatypes (Tree / Forest), each with a structural
// `decreases` on its datatype argument.
//
// STATUS (does NOT currently verify — matrix over-claims this row):
// Two compounding Strata-Core gaps surface:
//   1. "Undeclared type or category forest" — the mutually-recursive datatype
//      pair is emitted in declaration order, so `Tree` references `Forest`
//      before `Forest` is declared (no forward declaration of the sibling).
//   2. the same `@[cases]` structural-recursion gap as
//      structural_recursion.rs.
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
