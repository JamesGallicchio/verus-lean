# Boole handoff — bitvector arithmetic and unsigned comparison operators

## Summary

`Strata/Languages/Boole/Verify.lean:243`'s `toCoreTypedBin` is hardcoded
to require `ty = .int` and throws on any other type:

```lean
def toCoreTypedBin (m : SourceRange) (ty : Boole.Type) (op : String) (a b : Core.Expression.Expr) : TranslateM Core.Expression.Expr := do
  let .int _ := ty
    | throwAt m s!"Unsupported typed operator type: {repr ty}"
  …
```

Nine `toCoreExpr` arms route through it: `.add_expr`, `.sub_expr`,
`.mul_expr`, `.div_expr`, `.mod_expr`, `.le`, `.lt`, `.ge`, `.gt`.  All
of them are therefore **int-only**.  Boole has bv-specific AST nodes for
some operators — `.bvshl`, `.bvushr`, `.bvsshr`, `.bvand`, `.bvor`,
`.bvxor`, `.bvnot`, plus the *signed* arithmetic/comparison family
(`.bvsdiv`, `.bvsmod`, `.bvsle`, `.bvslt`, `.bvsge`, `.bvsgt`) — but
**no** unsigned counterparts (`.bvadd`, `.bvsub`, `.bvmul`, `.bvudiv`,
`.bvumod`, `.bvule`, `.bvult`, `.bvuge`, `.bvugt`) and **no** plain
arithmetic ops that would carry a bv-typed operand.

Any program that adds, subtracts, multiplies, takes unsigned
mod/div/comparison of bv values therefore fails Boole elaboration.

## Symptom

```
Unsupported typed operator type: Strata.BooleDDM.BooleType.bv32
  { start := { byteIdx := … }, stop := { byteIdx := … } }
```

(Same message with `bv8` / `bv16` / `bv64` for other widths.)  The
`byteIdx` range points at the *type* AST node Boole canonicalised, not
the operator that's actually failing — Boole reports the type witness,
not the call site.  In the SHA-256 compression test this is misleading
because the witness is in K32's `bv{32}(N)` literal chain, while the
real failures are in `rotate_right`'s `requires`/`assert` clauses (`bv32
<=`, `<`, `-`) and in `compress_u32`'s round body (`bv32 +` chains
produced by the wrapping-add inlining).

This is a load-bearing gap for crypto code: SHA-256 alone has

- 12 bv32 rotations per round × 64 rounds (depend on `bv{32}(32) - n`)
- ~8 bv32 wrapping-add operations per round × 64 rounds
- 8 final state-merge bv32 wrapping-adds per block

…all of which currently throw at the very first operator the elaborator
visits.

## Affected files

- `Strata/Languages/Boole/Verify.lean` — `toCoreTypedBin` (line 243),
  the nine `_expr` / inequality arms in `toCoreExpr` (lines 366–375).
- BooleDDM AST definitions for `Statement` / `Expr` — need new
  constructors paralleling the existing signed-bv ones.
- `Strata/Languages/Boole/Grammar.lean` — surface ops if the new bv
  nodes need any new keywords (most can reuse the existing `+`/`<`/etc.
  printers if dispatch happens at AST level).

## Reference patch shape

The pattern Boole already uses for **signed** bv comparison/division
applies cleanly: define a per-operator AST node, have `toCoreExpr` route
it through `toCoreBvBin`.  Extending to the missing nine ops is
mechanical:

```lean
-- Add to BooleDDM AST (existing signed family is the model):
| .bvadd  m ty a b      ← parallel to .bvsdiv / .bvsmod
| .bvsub  m ty a b
| .bvmul  m ty a b
| .bvudiv m ty a b
| .bvumod m ty a b
| .bvule  m ty a b      ← parallel to .bvsle / .bvslt / .bvsge / .bvsgt
| .bvult  m ty a b
| .bvuge  m ty a b
| .bvugt  m ty a b

-- Add to toCoreExpr (parallel to lines 380-388):
| .bvadd  m ty a b => toCoreBvBin m ty "Add"  (← toCoreExpr a) (← toCoreExpr b)
| .bvsub  m ty a b => toCoreBvBin m ty "Sub"  (← toCoreExpr a) (← toCoreExpr b)
| .bvmul  m ty a b => toCoreBvBin m ty "Mul"  (← toCoreExpr a) (← toCoreExpr b)
| .bvudiv m ty a b => toCoreBvBin m ty "UDiv" (← toCoreExpr a) (← toCoreExpr b)
| .bvumod m ty a b => toCoreBvBin m ty "UMod" (← toCoreExpr a) (← toCoreExpr b)
| .bvule  m ty a b => toCoreBvBin m ty "ULe"  (← toCoreExpr a) (← toCoreExpr b)
| .bvult  m ty a b => toCoreBvBin m ty "ULt"  (← toCoreExpr a) (← toCoreExpr b)
| .bvuge  m ty a b => toCoreBvBin m ty "UGe"  (← toCoreExpr a) (← toCoreExpr b)
| .bvugt  m ty a b => toCoreBvBin m ty "UGt"  (← toCoreExpr a) (← toCoreExpr b)
```

`toCoreBvBin` already exists (Verify.lean:262) and emits
`Bv{width}.{op}` in Core, which Core's SMT translation then maps to the
right SMT-LIB bv op.  No Core-side changes needed; this is purely a
Boole gap.

## Translator-side change (verus-lean)

Once the new AST nodes land, our nine builders in
`VerusLean/VLIR/Boole/Builder.lean` become one-line edits each.  Today
they reuse the int constructors with a bv type label:

```lean
def bvAdd  (w : Nat) (a b : BExpr) : BExpr := .add_expr default (bvTy w) a b   -- WRONG: int-only AST node
def bvSub  (w : Nat) (a b : BExpr) : BExpr := .sub_expr default (bvTy w) a b
def bvMul  (w : Nat) (a b : BExpr) : BExpr := .mul_expr default (bvTy w) a b
def bvUDiv (w : Nat) (a b : BExpr) : BExpr := .div_expr default (bvTy w) a b
def bvUMod (w : Nat) (a b : BExpr) : BExpr := .mod_expr default (bvTy w) a b
def bvUle  (w : Nat) (a b : BExpr) : BExpr := .le      default (bvTy w) a b
def bvUlt  (w : Nat) (a b : BExpr) : BExpr := .lt      default (bvTy w) a b
def bvUge  (w : Nat) (a b : BExpr) : BExpr := .ge      default (bvTy w) a b
def bvUgt  (w : Nat) (a b : BExpr) : BExpr := .gt      default (bvTy w) a b
```

After the patch:

```lean
def bvAdd  (w : Nat) (a b : BExpr) : BExpr := .bvadd  default (bvTy w) a b
def bvSub  (w : Nat) (a b : BExpr) : BExpr := .bvsub  default (bvTy w) a b
…
```

The asymmetry that gives the gap away today is local: the *signed*
counterparts (`bvSDiv`, `bvSMod`, `bvSle`, `bvSlt`, `bvSge`, `bvSgt`)
already use real bv-specific AST nodes (`.bvsdiv`, `.bvsmod`, `.bvsle`,
…) — see Builder.lean:126-148.  So someone added the signed bv AST
nodes at some point but never the unsigned/non-signedness-marked ones,
and our builders papered over the difference by reusing the int
constructors.

## Test idea

Five-line repro:

```
program Boole;

procedure simple_bv_add (x : bv32, y : bv32) returns (out : bv32)
spec { } {
  out := x + y;
};
```

Today this fails to elaborate with `Unsupported typed operator type:
BooleType.bv32`.  After the patch it should elaborate cleanly and lower
to SMT `bvadd`.  Add similar one-line cases per operator (`-`, `*`,
`/`, `mod`, `<`, `<=`, `>`, `>=`).

## Notes

- **A translator-only cast workaround is wrong by construction.**
  Casting `bv → int → int_op → int → bv` looks attractive — the
  `bv*_to_int_u` / `int_to_bv*_u` helpers already exist — but it
  destroys 2's-complement wrapping semantics.  E.g., `(2^32 - 1) + 1`
  evaluates to `2^32` in math-int (no wrap) and to `0` in bv32 (wrap).
  SHA-256 (and every other crypto algorithm) depends on the wrap.  The
  fix has to be on the AST side; we cannot work around it in our
  emission.
- **`bvSDiv` / `bvSMod` already exist as separate AST nodes** in BooleDDM
  and in `toCoreBvBin`'s dispatch — see Verify.lean line 380-388 for
  the existing signed-comparison family, and Builder.lean:126-127 for
  the existing signed div/mod builders.  The new constructors should
  parallel that exact shape.
- **Constants on the RHS of shifts already work** because `.bvshl` /
  `.bvushr` / `.bvsshr` are routed through `toCoreBvBin`, which doesn't
  go through the int-only `toCoreTypedBin`.  The bv arithmetic gap is
  specifically the *typed binop* family.
- **Coverage caveat for handoff scope**: if/when Boole grows a
  systematic Core-coverage test (see notes elsewhere), this gap would
  have been caught the day Core gained bv arithmetic support — Core has
  had bv ops for a long time, but Boole's surface only partially
  mirrored them.  Worth flagging at the same time as this fix.
