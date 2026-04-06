// Vec prelude: models Rust Vec<T> as a datatype wrapping Map bv64 T + length.
//
// Only the datatype and pure accessors are defined here.  Mutation operations
// (push, pop, set, append, insert, remove, swap_remove, etc.) come from the 
// Verus SST as procedure stubs with ensures clauses — they reference Vec_view 
// to connect the datatype to Strata's built-in Sequence type.

datatype Vec (T: Type) { Vec_ctor(Vec_data: Map bv64 T, Vec_len: bv64) };

function Vec_len<T>(v: Vec T): bv64 {
  Vec..Vec_len(v)
}

function Vec_index<T>(v: Vec T, i: bv64): T {
  (Vec..Vec_data(v))[i]
}

// --- Ghost view: connects Vec to Sequence (abstract) ---
// Semantics given by ensures clauses of Vec_new, Vec_push, etc.

function Vec_view<T>(v: Vec T): Sequence T;
