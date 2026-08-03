# Seq and Vec Translation Pipeline

This document describes the **live** Seq/Vec translation path in
`verus-boogie`: which pieces come directly from Verus SST (JSON), which come
from the text Seq prelude, which are synthesized by the translator, and which
operations lower directly to Boole/Strata built-ins without emitting
declarations.

The active prelude model remains **text-first**:
- `prelude/Seq.boole.st` and `prelude/Vec.boole.st` are both part of the live
  translation path and may be prepended to emitted output.
- If a lowered program needs a text prelude and the corresponding prelude file
  is absent, that is a configuration problem; the live path no longer treats
  stale generated Core files as the prelude source of truth.

The Lean translator separately carries exact metadata about:
- which names are provided by the Seq prelude
- which Seq names inline directly to `Sequence.*`
- which translator-generated numeric/support decls are synthesized internally

That metadata is used for type inference, Seq-prelude need detection,
and duplicate filtering.

Prelude loading is planned from VLIR syntax before BooleDDM construction.  The
translator no longer performs a probe translation just to discover incidental
free-variable references, so prelude selection is independent of fvar allocation
side effects.

Checked-in generated files under `tests/BoogieFiles/` and `tests/BooleFiles/`
are **snapshots**, not the normative specification of the current pipeline.
They are useful regression fixtures and examples, but they can lag behind the
live translator until a test is rerun. For architectural questions, prefer the
current lowering code plus freshly regenerated outputs over an arbitrary
checked-in artifact.

## Overview

Verus `Seq<T>` maps to Strata's built-in `Sequence T` type.
Verus `Vec<T>` lowers through the Vec prelude datatype:
- the main Vec value has type `Vec T`
- the prelude owns the accessor names `Vec_len`, `Vec_index`, and `Vec_view`
- `Vec_len` and `Vec_index` are defined in the prelude with simple projection bodies
- source-facing ghost views use the abstract prelude helper `Vec_view(v)`

Seq/Vec-related support reaches the emitted program through three declaration
supply paths, plus one direct non-declaration lowering path:

1. **Verus SST (JSON)** — provides the source-facing API surface that Verus
   actually exported.  For Seq/Vec, this mainly contributes declaration-only
   procedure stubs for Vec mutation operations (`push`, `pop`, `set`,
   `append`, `insert`, `remove`, `swap_remove`) via Verus
   `assume_specification` declarations in `vstd/std_specs/vec.rs`.

2. **Prelude files** (`prelude/Seq.boole.st`, `prelude/Vec.boole.st`) — provide
   text-first Boole declarations for shared Seq/Vec helper types and functions
   that are not recovered directly from the JSON. The Vec prelude owns the
   datatype plus the accessor names `Vec_len`, `Vec_index`, and `Vec_view`.

3. **Translator-generated** — the translator recognizes some Seq/Vec shapes
   directly during lowering and synthesizes small support declarations on
   demand when the JSON and text preludes do not already provide them. This
   covers numeric support (`nat`, `nat_to_int`, `int_to_nat`), bitvector cast
   helpers, and collection support decls, but not the pure Vec accessors.

4. **Direct built-in lowering (no declaration emitted)** — some Seq
   operations are translated straight to `Sequence.*` expressions in the
   emitted Boole program, so they affect behavior without contributing any new
   declaration.

These are not disjoint provenance buckets for the whole program. They overlap
at the symbol-family level:
- the `Vec` story is intentionally split between JSON-exported mutation
  procedure stubs and Vec-prelude-owned pure accessors like `Vec_view`
- Seq-prelude-provided names and translator support declarations can overlap
  by exact name, in which case the active prelude declaration is kept

They are also not a complete partition of all translated declarations:
- ordinary user/program declarations still come from the main JSON-to-Boole
  lowering pipeline
- the four paths above are only meant to explain the Seq/Vec-specific support
  layer

## Seq Operations

### Inlined to Strata Built-ins

When the translator encounters a Verus Seq method call (e.g., `Seq::push`),
it is sanitized to a name like `Seq_push`, then translated **inline** to the
corresponding Strata `Sequence.*` built-in.  No function declaration is
emitted — the built-in call appears directly in the output expression.

| Verus SST name     | Boole output                                             |
|---------------------|----------------------------------------------------------|
| `Seq_index(s, i)`   | `Sequence.select(s, i)`                                  |
| `Seq_push(s, x)`    | `Sequence.build(s, x)`                                   |
| `Seq_empty()`       | `Sequence.empty`                                         |
| `Seq_update(s,i,v)` | `Sequence.update(s, i, v)`                               |
| `Seq_take(s, n)`    | `Sequence.take(s, n)`                                    |
| `Seq_skip(s, n)`    | `Sequence.drop(s, n)`                                    |
| `Seq_add(s1, s2)`   | `Sequence.append(s1, s2)`                                |
| `Seq_first(s)`      | `Sequence.select(s, 0)`                                  |
| `Seq_last(s)`       | `Sequence.select(s, Sequence.length(s) - 1)`             |
| `Seq_subrange(s,a,b)` | `Sequence.take(Sequence.drop(s, a), b - a)`            |
| `Seq_lib_contains`  | `Sequence.contains(s, v)`                                |
| `Seq_lib_drop_last` | `Sequence.take(s, Sequence.length(s) - 1)`               |
| `Seq_lib_remove`    | `Sequence.append(Sequence.take(s,i), Sequence.drop(s,i+1))` |

### On-Demand Support Declarations

Functions that cannot be expressed as Strata built-in calls are emitted on
demand by `VerusLean/VLIR/Boole/SupportEmit.lean`. They are abstract.
`prelude/Seq.boole.st` is intentionally almost empty; emitting polymorphic
helpers only when referenced avoids unused-type-variable encoding failures.

| Function              | Why abstract?                        |
|-----------------------|--------------------------------------|
| `Seq_new(len, f)`     | Requires higher-order iteration      |
| `Seq_lib_map(s, f)`   | Higher-order iteration               |
| `Seq_lib_map_values`  | Higher-order iteration               |
| `Seq_lib_filter`      | Higher-order iteration               |
| `Seq_lib_sort_by`     | Higher-order iteration               |
| `Seq_lib_zip_with`    | Higher-order iteration               |
| `Seq_lib_to_set`      | No native Strata Set conversion      |
| `Set_finite`          | No native Strata Set finiteness test |

The on-demand support layer also provides:
- `type Set (T: Type);` — used by `Seq_lib_to_set`

The always-loaded Nat prelude provides:
- `type nat;`
- `function nat.toInt(n: nat): int;`
- `function nat.fromInt(i: int): nat requires 0 <= i;`
- round-trip and non-negativity axioms for those conversions

`Seq_len`, `Seq_lib_insert`, and `Seq_subrange` no longer need declarations:
current translation paths inline or lower those operations before a standalone
helper declaration is needed.

### Missing Prelude Files

The live Boole pipeline treats the text preludes as the maintained model.  If a
needed prelude is missing, fix the prelude configuration rather than relying on
old generated `.core.st` snapshots.

## Vec Operations

### Representation

The live translator uses the Vec prelude datatype:

- a Vec-typed variable `v : Vec<T>` lowers to a Boole variable `v : Vec T`
- procedure headers and local declarations keep that datatype directly
- ghost/spec-facing sequence views go through the abstract prelude helper
  `Vec_view(v) : Sequence T`

### Vec Expression Lowering (Translator)

When the translator encounters Vec operations in expressions:

| Verus SST call                   | Boole output                        |
|----------------------------------|-------------------------------------|
| `view::View::view(v)` on a Vec  | `Vec_view(v)`                       |
| `spec_vec_len(v)` or `vec::len` | `Vec_len(v)`                        |
| `vec_index(v, i)` or `Seq::index(view(v), i)` | `Vec_index(v, i)` |

The translator unwraps `view()` calls: `Seq::len(view(v))` becomes
`Vec_len(v)`, not `Seq_len(Vec_view(v))`.

### Vec Mutation Procedures (from JSON)

Vec mutation operations appear in the Verus SST as `ExecFn` declarations
with `has_body=False` and ensures clauses derived from Verus's
`assume_specification` in `vstd/std_specs/vec.rs`.  The translator emits
these as **body-less procedure stubs** — Strata treats the ensures as
trusted axioms at call sites.

| Verus SST declaration          | Boole procedure (conceptually) | Ensures (after Vec lowering)                    |
|---------------------------------|-------------------------------|--------------------------------------------------|
| `vec::impl&%0::new`            | `Vec_new<T>()`                | `Vec_view(v) == Sequence.empty`                  |
| `vec::impl&%1::push`           | `Vec_push<T>(vec, val)`       | `Vec_view(out) == Sequence.build(Vec_view(vec), val)` |
| `vec::impl&%1::pop`            | `Vec_pop<T>(vec)`             | guards on `Vec_len(vec) > 0`; uses `Sequence.take` |
| `pervasive::impl&%0::set`      | `Pervasive_set(vec, i, val)`  | `Vec_view(out) == Sequence.update(...)`          |
| `vec::impl&%1::append`         | `Vec_append<T>(vec, other)`   | `Vec_view(out) == Sequence.append(...)`          |
| `vec::impl&%1::insert`         | `Vec_insert<T>(vec, i, elem)` | `Vec_view(out) == Seq_lib_insert(...)`           |
| `vec::impl&%1::remove`         | `Vec_remove<T>(vec, i)`       | uses `Sequence.take`/`Sequence.drop`             |
| `vec::impl&%1::swap_remove`    | `Vec_swap_remove<T>(vec, i)`  | uses `Sequence.update`/`Sequence.take`           |

These procedures are **not** in the prelude — they are generated from the
SST during translation. If the Verus source file does not import
`vstd::std_specs::vec`, the corresponding declarations will be absent.

### Executable `Vec::push`

Verus specifies push as `vec@ == old(vec)@.push(value)`. Because Vec is already
a Sequence in Boole, the executable call is lowered without a procedure stub:

```boole
vec := Sequence.build(vec, value);
```

The SST represents a borrow through a mutable-reference prophecy temporary.
Before statement lowering, the translator aliases that compiler temporary back
to the owning vector, ensuring the assignment updates the program-visible
variable. `Vec_push` itself is then filtered from the output.

The regression example `tests/VerusFiles/unit_tests/vec_push.rs` checks the
complete contract and generates `out_ := Sequence.build(out_, value)`. Other
Vec mutation operations remain subject to their individual direct-lowering
support; an unrecognized residual `Vec_*` call is currently dropped.


### Executable `Vec::new` and `Vec::with_capacity`

Neither has an exported Verus declaration — they are compiler intrinsics — so
there is no procedure stub to call. Both construct an empty vector (a capacity
hint does not affect the length), and with `Vec := Sequence` they lower to the
empty sequence, taking the element type from the binding's expected type:

```boole
v := Sequence.empty_bv64;
```

Element types with no dedicated typed token (tuples, structs, type parameters)
use the polymorphic `Sequence.empty<T>()` form; see `seqEmptyTokenName?`.

### Recognized Operations Precede the `Vec_*` Drop

Residual `Vec_*` calls are dropped (`isVec2SeqDroppedCalleeName`) because their
declarations are filtered from the output and a call site would dangle. That
rule matches on the `Vec_` prefix, so it also matches the names of operations
that *do* have lowerings — `Vec_len`, `Vec_push`. Every recognized operation is
therefore checked **before** the drop, in both the bare-call and
assignment-RHS paths of `stmToBoole`.

Dropping first is silent rather than loud: the statement disappears and the
assigned variable keeps an arbitrary value, so `let n = v.len(); assert(n ==
v.len())` fails with no diagnostic. Nested uses (loop conditions, asserts) go
through the expression path, which has no drop rule — so a mis-ordering shows
up only when the call is an assignment's entire right-hand side.

### Name Canonicalization

Verus internal `impl` block names (e.g., `vec::impl&%1::push`) are
canonicalized by `stripImplSegment`, which removes `_Impl__N_` segments:
`Vec_Impl__1_push` → `Vec_push`, `Option_Impl__0_unwrap` → `Option_unwrap`.

## Prelude Inclusion Logic

1. `Main.lean` probes `declsToBooleProgram` to compute text-prelude needs
   from emitted Boole references using exact trigger manifests:
   - Seq prelude is needed if any Seq-prelude trigger type/value is referenced
   - Vec prelude is needed if any Vec-prelude trigger type/value is referenced

2. In `Main.lean`, the requested Seq and Vec prelude texts are prepended in
   that order.

3. Declarations provided by the active Seq/Vec preludes are filtered from the
   translator output by exact name.

4. Type inference for Seq-prelude-provided names and direct built-in lowering
   still uses Lean-side metadata tables so lowering can assign expected types
   before the textual prelude is spliced in.

## Pretty-Printing Notes

- `Sequence.select(s, i)` and `Sequence.update(s, i, v)` must be printed
  as **function calls**, not bracket syntax (`s[i]`, `s[i := v]`).  Strata's
  DDM parser interprets bracket syntax as Map operations only.
- Map select/update (`m[k]`, `m[k := v]`) use bracket syntax.

## Design Notes & Open Trade-offs

This section records design decisions and the reasoning behind them, so we
don't relitigate them every time someone notices an asymmetry in the output.

### `v.len()` dispatch: built-in vs prelude wrapper

When the translator sees `v.len()` on a `Vec<T>`, it emits
`Sequence.length(v)` directly (with a numeric coercion), bypassing the
prelude's `Seq_len` wrapper. The dispatch happens at
[`Translate.lean:655-666`](../VerusLean/VLIR/Boole/Translate.lean) under the
`isVecLenSpecName || isVecLenExecName` branch.

Consequence: the `Seq_len` declaration in `prelude/Seq.boole.st` is dead
weight for tests that only call `v.len()` on Vec values (e.g. `demo_for`'s
`find_max`, where `Seq_len` is declared but never referenced in the body).
The prelude is still pulled in because `Seq_len` is in `seqTriggerNames`,
even though no body will use it.

**Why we keep this asymmetry**:
- `Sequence.length(v) : int` is a Strata primitive cvc5 reasons about
  natively. Going through `Seq_len(v) = int_to_nat(Sequence.length(v))`
  introduces a `nat` round-trip via the abstract `nat` type, which erases
  the integer-arithmetic axioms cvc5 has on `Sequence.length`.
- Verus's `Vec::len() : usize` callers expect a `bv64`-shaped result for
  comparisons/arithmetic. The translator inserts the cast at the call site
  via `coerceNumeric`. Wrapping through `Seq_len` would compose
  `nat → int → bv64`, which is two coercion fns chained for no semantic
  win.

**If we ever do switch**: this would only be safe once `nat` is a Strata
primitive (or once `int_to_nat ∘ Sequence.length` is axiomatized to behave
like `Sequence.length` on non-negative inputs). Until then, switching
regresses tests that rely on cvc5's reasoning about `Sequence.length` as
an integer.

**Cheap interim cleanup**: remove `Seq_len` (and `Seq_lib_insert`) from
[`seqTriggerNames`](../VerusLean/VLIR/Boole/Prelude.lean) so the prelude
isn't pulled in by callers that only end up emitting `Sequence.length`.
This isolates the prelude to tests that genuinely need its abstract
higher-order declarations.

### Per-function prelude gating

Today the prelude is gated whole-file: any Seq trigger pulls in all 43
lines of `Seq.boole.st`. We considered finer per-function gating (only
emit `Seq_len` if `Seq_len` is referenced, etc.) but rejected it.

**Cost**: ~150 lines of Lean in `Prelude.lean` plus a transitive-dependency
graph (`Seq_len → int_to_nat → nat`, `Set_finite → Set`), built either by
hand (brittle) or by parsing the prelude operations after `loadPrelude`.

**Benefit**: ~25-30 lines of output reduction in Seq-using tests; zero
benefit for tests that already get no prelude.

**When it would pay off**:
1. An unreferenced abstract decl (e.g. `Seq_lib_sort_by`'s higher-order
   signature) trips a Strata-side error and breaks every Seq test.
2. The prelude grows beyond ~100 lines.
3. We want demo-quality minimal Boole output for documentation.

**Decision**: don't build it now. Revisit when one of the forcing
functions above appears.

### Translation directness vs source faithfulness

The general translator preference for Seq operations: when a Strata
built-in is name-recognizable from the Verus call, emit the built-in
directly. The prelude wrapper exists only as a fallback for
unrecognized names and as a place to declare higher-order operations
(`Seq_lib_map`, `Seq_lib_filter`, `Seq_lib_sort_by`, `Seq_new`,
`Seq_lib_to_set`, `Set_finite`) that have no first-order built-in
equivalent.

Source-faithfulness loss from this choice: a `Seq_len(s)` call in source
becomes `Sequence.length(s)` in output, and the wrapper's `nat` return
type is replaced by an `int` with downstream coercion. The `nat`
distinction is erased on the way down.

This is the same class of erasure as Rust `let` vs `let mut` — recorded
once in `tests/differential_status.md`'s preamble — where the target
language's representation simply doesn't carry the source-level
distinction. Verification semantics are preserved; lexical fidelity is
not.
