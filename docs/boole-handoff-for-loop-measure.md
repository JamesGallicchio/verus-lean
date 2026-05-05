# Boole handoff — For-loop measure clause

## Summary

`for v := init to limit ... { body }` and `for v := init downto limit ... { body }`
have no syntactic slot for a `decreases` measure, so any user-supplied
termination measure is dropped at parse time.  Lowered loops always carry
`measure := none` into Core, which forces the verifier to re-derive
termination from the loop bound alone.

## Symptom

The `verus-lean` translator drops user-written `decreases` clauses on every
range loop.  The omission is documented in
[`VerusLean/VLIR/Boole/Translate.lean`](https://github.com/.../VerusLean/VLIR/Boole/Translate.lean):

> `Strata's `for_to_by` / `for_down_to_by` grammar has no measure slot
> (tracked upstream in our `add-for-loop-measure-clause` branch).`

The SHA-256 compression test (`tests/scratch/sha256_compact_indexed.rs`) has
two range loops (`for i in 0..16` in `to_u32s` and `for i in 0..64` in
`compress_u32`) whose Verus-synthesized `decreases` clauses are silently
discarded.  The user-written `decreases blocks.len() - k` on the indexed
`compress` loop survives because that loop is a `while`, not a `for`.

## Affected files

- `Strata/Languages/Boole/Grammar.lean` — `for_to_by_statement` and
  `for_down_to_by_statement` productions
- `Strata/Languages/Boole/Verify.lean` — `lowerFor` and the two `for_to_by`
  / `for_down_to_by` arms of `toCoreStmt`

## Reference patch

Our local branch carries the change as commit `f9387373d` (subject:
"Local Boole patches: for-loop measure clause, ...").  The grammar diff
is small:

```diff
-op for_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
-  @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
+op for_to_by_statement (v : MonoBind, init : Expr, limit : Expr,
+  @[scope(v)] measure : Option Measure, @[scope(v)] step : Option Step, @[scope(v)] invs : Invariants,
   @[scope(v)] body : Block) : Statement =>
-  "for " v " := " init " to " limit step invs body;
+  "for " v " := " init " to " limit step "\n" measure:0 invs body "\n";
```

The lowering side adds:

```lean
private def toCoreMeasure? :
    Option (BooleDDM.Measure SourceRange) → TranslateM (Option Core.Expression.Expr)
  | none => return none
  | some (.measure_mk _ e) => return some (← toCoreExpr e)
```

and threads a `measure : Option Core.Expression.Expr` argument through
`lowerFor` into the Core `loop` measure field.

## Test idea

A minimal regression — any range loop with a non-trivial `decreases`:

```rust
fn loop_with_measure(n: u32) {
    let mut i: u32 = 0;
    while i < n
        invariant i <= n,
        decreases n - i,
    { i = i + 1; }
}
```

(While-loop measures already work; the grammar gap only bites range
loops, so the regression test should use `for` syntax in the Boole-level
input where the parser produces `for_to_by_statement`.)

## Notes

- `for_statement` (the C-style `for (v := init; guard; step) ...`) does
  not need a measure slot in the same way because the user can write the
  measure as part of the `step` expression — but if you want consistency,
  threading a `measure` parameter through that production too is a clean
  symmetry.
- The lowering should preserve `measure := none` behaviour for sources
  that don't supply a `decreases` clause (the Verus front end leaves it
  off when the bound is trivially decreasing).
