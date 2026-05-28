/-
  Boole.Cast — BuildM-valued cast-insertion helpers.

  These helpers thread the translator's state (via `BuildM`) to resolve cast
  helpers as free variables and register required support declarations. They
  sit atop the pure-type primitives in `Coercions`, which stay IO-free so
  metadata modules (e.g. `Signatures`) can depend on them without pulling
  `Strata.Util.IO` transitively.
-/
import VerusLean.VLIR.Boole.Bld
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.Support

namespace VerusLean.Boole.Cast

open VerusLean
open VerusLean.Boole.Bld
open VerusLean.Boole.Coercions
open VerusLean.Boole.Emit
open VerusLean.Boole.Support

/-- Resolve a cast helper to a `BExpr` (free variable). -/
private def castFnExpr (need : SupportDecl) : BuildM BExpr := do
  let idx ← resolveFreeVar (supportDeclName need)
  pure (Bld.fvar idx)

/-- Apply a unary cast helper.  Most cast kinds are emitted as calls to a
    bodyless support-decl function (`bv8_to_int_u`, `int_to_nat`, …) that
    gets axiomatized at the call site.  `.bvToInt` is special-cased to
    emit Strata's native `(e as_int)` / `(e as_sint)` postfix instead,
    which lowers to `Bv<W>.ToUInt`/`Bv<W>.ToInt` at Core — cvc5's bv
    theory then proves nonneg-ness of unsigned bv→int by construction,
    making an explicit `bv<W>_to_int_u_nonneg` axiom unnecessary. -/
def applyCast (need : SupportDecl) (e : BExpr) : BuildM BExpr := do
  match need with
  | .bvToInt w signed =>
    if signed then pure (Bld.castToSInt (Bld.bvTy w) e)
    else pure (Bld.castToInt (Bld.bvTy w) e)
  | _ =>
    requireSupport need
    if supportDeclUsesNat need then
      requireSupport .nat
    let fn ← castFnExpr need
    pure (Bld.app fn e)

private def castExprToWiderBvB (fromW toW : Nat) (signed : Bool) (e : BExpr) : BuildM BExpr := do
  if fromW == toW then pure e
  else applyCast (.bvWiden fromW toW signed) e

/-- Extract an explicit bitvector width from a `BType` annotation. -/
private def bvTypeWidth? : BType → Option Nat
  | .bv1 _ => some 1
  | .bv8 _ => some 8
  | .bv16 _ => some 16
  | .bv32 _ => some 32
  | .bv64 _ => some 64
  | _ => none

/-- Width of a `BExpr` that carries a bv type syntactically (typed bv ops +
    bv literals). Defense-in-depth: lets `coerceBvBv` / `coerceNumeric`
    short-circuit if the caller's `srcInfo?` hint ever drifts from the
    translated BExpr's actual width. Returns `none` on `.app` / `.fvar` /
    `.bvar` — caller falls back to the hint. -/
private def bexprBvWidth? : BExpr → Option Nat
  | .bv1Lit ..  => some 1
  | .bv8Lit ..  => some 8
  | .bv16Lit .. => some 16
  | .bv32Lit .. => some 32
  | .bv64Lit .. => some 64
  | .add_expr _ ty _ _ | .sub_expr _ ty _ _ | .mul_expr _ ty _ _
  | .div_expr _ ty _ _ | .mod_expr _ ty _ _
  | .bvsdiv _ ty _ _ | .bvsmod _ ty _ _
  | .neg_expr _ ty _
  | .bvand _ ty _ _ | .bvor _ ty _ _ | .bvxor _ ty _ _
  | .bvnot _ ty _
  | .bvshl _ ty _ _ | .bvushr _ ty _ _ =>
    bvTypeWidth? ty
  | _ => none

/-- Positive detector for `BExpr`s that are known to be int-typed.

    This only returns true when the emitted BooleDDM node carries an explicit
    `.int` type tag. Unknown shapes such as `.app`, `.fvar`, and `.bvar`
    return false, so callers default to applying the requested cast. -/
private def bexprIsKnownInt : BExpr → Bool
  | .add_expr _ (.int _) _ _ | .sub_expr _ (.int _) _ _
  | .mul_expr _ (.int _) _ _ | .div_expr _ (.int _) _ _
  | .mod_expr _ (.int _) _ _ | .neg_expr _ (.int _) _ => true
  | _ => false

/-- Insert a single numeric coercion. Returns the expression unchanged when
    no coercion is needed. -/
def coerceNumeric (src? target? : Option NumKind) (e : BExpr) :
    BuildM BExpr :=
  match src?, target? with
  | _, none | none, _ => pure e
  | some src, some target =>
    if src == target then pure e
    else match src, target with
    | .bv w s, .int =>
      if bexprIsKnownInt e then pure e
      else applyCast (.bvToInt w s) e
    | .bv w s, .nat => applyCast (.bvToNat w s) e
    | .nat, .int => applyCast .natToInt e
    | .int, .bv w s => applyCast (.intToBv w s) e
    | .nat, .bv w s => do
      let eInt ← applyCast .natToInt e
      applyCast (.intToBv w s) eInt
    | .bv sw ss, .bv tw ts =>
      let effSw := bexprBvWidth? e |>.getD sw
      if effSw == tw then pure e
      else if ss == ts && canPromoteBvWidths effSw tw then
        castExprToWiderBvB effSw tw ss e
      else do
        let eInt ← applyCast (.bvToInt effSw ss) e
        applyCast (.intToBv tw ts) eInt
    | .int, .nat => applyCast .intToNat e
    | .int, .int | .nat, .nat => pure e

/-- Coerce between bitvector widths when both source and target are known.
    Prefers `bexprBvWidth? e` over `srcInfo?` when available. -/
def coerceBvBv (srcInfo? targetInfo? : Option (Nat × Bool)) (e : BExpr) :
    BuildM BExpr := do
  match srcInfo?, targetInfo? with
  | some (sw, ss), some (tw, ts) =>
    let effSw := bexprBvWidth? e |>.getD sw
    if effSw == tw then pure e
    else if ss == ts && canPromoteBvWidths effSw tw then
      castExprToWiderBvB effSw tw ss e
    else do
      let eInt ← applyCast (.bvToInt effSw ss) e
      applyCast (.intToBv tw ts) eInt
  | _, _ => pure e

end VerusLean.Boole.Cast
