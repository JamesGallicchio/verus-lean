# Seq and Vec Translation Pipeline

This document describes the **live** Seq/Vec translation path in
`verus-boogie`: which pieces come directly from Verus SST (JSON), which come
from the text Seq prelude, which are synthesized by the translator, and which
operations lower directly to Core built-ins without emitting declarations.

The active prelude model remains **text-first**:
- `prelude/Seq.core.st` and `prelude/Vec.core.st` are both part of the live
  translation path and may be prepended to emitted output.
- Seq still has a degraded internal fallback when its text prelude is absent.
- Vec currently does not have such a fallback; if the lowered program needs
  Vec support, `prelude/Vec.core.st` must be available.

The Lean translator separately carries exact metadata about:
- which names are provided by the Seq prelude
- which Seq names inline directly to `Sequence.*`
- which translator-generated numeric/support decls are synthesized internally

That metadata is used for type inference, Seq-prelude need detection,
duplicate filtering, and the degraded Seq fallback path.

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

2. **Prelude files** (`prelude/Seq.core.st`, `prelude/Vec.core.st`) — provide
   text-first Core declarations for shared Seq/Vec helper types and functions
   that are not recovered directly from the JSON. The Vec prelude owns the
   datatype plus the accessor names `Vec_len`, `Vec_index`, and `Vec_view`.

3. **Translator-generated** — the translator recognizes some Seq/Vec shapes
   directly during lowering and synthesizes small support declarations on
   demand when the JSON and text preludes do not already provide them. This
   covers numeric support (`nat`, `nat_to_int`, `int_to_nat`), bitvector cast
   helpers, and collection support decls, but not the pure Vec accessors. The
   only degraded fallback path is still for the Seq prelude.

4. **Direct built-in lowering (no declaration emitted)** — some Seq
   operations are translated straight to `Sequence.*` expressions in the
   emitted Core program, so they affect behavior without contributing any new
   declaration.

These are not disjoint provenance buckets for the whole program. They overlap
at the symbol-family level:
- the `Vec` story is intentionally split between JSON-exported mutation
  procedure stubs and Vec-prelude-owned pure accessors like `Vec_view`
- Seq-prelude-provided names and translator fallback declarations can overlap
  by exact name, in which case the fallback is only used when the text Seq
  prelude is unavailable

They are also not a complete partition of all translated declarations:
- ordinary user/program declarations still come from the main JSON-to-Core
  lowering pipeline
- the four paths above are only meant to explain the Seq/Vec-specific support
  layer

## Seq Operations

### Inlined to Strata Built-ins

When the translator encounters a Verus Seq method call (e.g., `Seq::push`),
it is sanitized to a name like `Seq_push`, then translated **inline** to the
corresponding Strata `Sequence.*` built-in.  No function declaration is
emitted — the built-in call appears directly in the output expression.

| Verus SST name     | Core output                                              |
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

### Declared in Seq Prelude

Functions that cannot be expressed as Strata built-in calls are declared in
`prelude/Seq.core.st`.  Some have concrete bodies; others are abstract.

| Function              | Body                                         | Why abstract?                        |
|-----------------------|----------------------------------------------|--------------------------------------|
| `Seq_len(s)`          | `int_to_nat(Sequence.length(s))` (concrete)  | —                                    |
| `Seq_lib_insert(s,i,v)` | `Sequence.append(Sequence.build(Sequence.take(s,i),v), Sequence.drop(s,i))` (concrete) | — |
| `Seq_new(len, f)`     | abstract                                     | Requires iteration — not expressible in Core function syntax |
| `Seq_lib_map(s, f)`   | abstract                                     | Higher-order iteration               |
| `Seq_lib_map_values`  | abstract                                     | Higher-order iteration               |
| `Seq_lib_filter`      | abstract                                     | Higher-order iteration               |
| `Seq_lib_sort_by`     | abstract                                     | Higher-order iteration               |
| `Seq_lib_to_set`      | abstract                                     | No Strata Set built-in               |
| `Set_finite`          | abstract                                     | No Strata Set built-in               |

The Seq prelude also provides:
- `type Set (T: Type);` — used by `Seq_lib_to_set`

The translator-managed numeric support layer provides:
- `type nat;`
- `function nat_to_int(n: nat): int;`
- `function int_to_nat(i: int): nat;`

Those declarations are emitted from the same support assembly as the other
translator-generated cast helpers, so later nat-using features do not depend
on the Seq prelude just to get the `nat` bridge functions.

### Fallback Path (No Prelude File)

If `prelude/Seq.core.st` is absent, the translator generates equivalent
**abstract** function stubs via `neededSeqPreludeFallbackDecls`, using the
Seq-prelude portion of the translator's known-function registry. These stubs
have no concrete bodies — the fallback path is a degraded mode.

There is currently **no degraded fallback** for the live Vec path. Vec support
requires the text Vec prelude.

## Vec Operations

### Representation

The live translator uses the Vec prelude datatype:

- a Vec-typed variable `v : Vec<T>` lowers to a Core variable `v : Vec T`
- procedure headers and local declarations keep that datatype directly
- ghost/spec-facing sequence views go through the abstract prelude helper
  `Vec_view(v) : Sequence T`

### Vec Expression Lowering (Translator)

When the translator encounters Vec operations in expressions:

| Verus SST call                   | Core output                         |
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

| Verus SST declaration          | Core procedure (conceptually) | Ensures (after Vec lowering)                     |
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

### Name Canonicalization

Verus internal `impl` block names (e.g., `vec::impl&%1::push`) are
canonicalized by `stripImplSegment`, which removes `_Impl__N_` segments:
`Vec_Impl__1_push` → `Vec_push`, `Option_Impl__0_unwrap` → `Option_unwrap`.

## Prelude Inclusion Logic

1. `declsToProgram` computes structured text-prelude needs from the emitted
   Core references using exact trigger manifests:
   - Seq prelude is needed if any Seq-prelude trigger type/value is referenced
   - Vec prelude is needed if any Vec-prelude trigger type/value is referenced

2. If the text Seq prelude is unavailable, `neededSeqPreludeFallbackDecls`
   synthesizes abstract fallback declarations for the Seq-prelude-owned names.

3. If the text Vec prelude is unavailable when needed, translation fails fast.

4. In `Main.lean`, the requested Seq and Vec prelude texts are prepended in
   that order.

5. Declarations provided by the active Seq/Vec preludes are filtered from the
   translator output by exact name.

6. Type inference for Seq-prelude-provided names and direct built-in lowering
   still uses Lean-side metadata tables so lowering can assign expected types
   before the textual prelude is spliced in.

## Pretty-Printing Notes

- `Sequence.select(s, i)` and `Sequence.update(s, i, v)` must be printed
  as **function calls**, not bracket syntax (`s[i]`, `s[i := v]`).  Strata's
  DDM parser interprets bracket syntax as Map operations only.
- Map select/update (`m[k]`, `m[k := v]`) use bracket syntax.
