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

namespace VerusLean.Boole.Cast

open VerusLean
open VerusLean.Boole.Bld
open VerusLean.Boole.Coercions
open VerusLean.Boole.Emit

/-- Resolve a cast helper to a `BExpr` (free variable). -/
private def castFnExpr (need : SupportDecl) : BuildM BExpr := do
  let idx ← resolveFreeVar (supportDeclName need)
  pure (Bld.fvar idx)

/-- Apply a unary cast helper and record the required support declaration. -/
def applyCast (need : SupportDecl) (e : BExpr) : BuildM BExpr := do
  requireSupport need
  if supportDeclUsesNat need then
    requireSupport .nat
  let fn ← castFnExpr need
  pure (Bld.app fn e)

private def castExprToWiderBvB (fromW toW : Nat) (signed : Bool) (e : BExpr) : BuildM BExpr := do
  if fromW == toW then pure e
  else applyCast (.bvWiden fromW toW signed) e

/-- Insert a single numeric coercion. Returns the expression unchanged when
    no coercion is needed. -/
def coerceNumeric (src? target? : Option NumKind) (e : BExpr) :
    BuildM BExpr :=
  match src?, target? with
  | _, none | none, _ => pure e
  | some src, some target =>
    if src == target then pure e
    else match src, target with
    | .bv w s, .int => applyCast (.bvToInt w s) e
    | .bv w s, .nat => applyCast (.bvToNat w s) e
    | .nat, .int => applyCast .natToInt e
    | .int, .bv w s => applyCast (.intToBv w s) e
    | .nat, .bv w s => do
      let eInt ← applyCast .natToInt e
      applyCast (.intToBv w s) eInt
    | .bv sw ss, .bv tw ts =>
      if ss == ts && canPromoteBvWidths sw tw then
        castExprToWiderBvB sw tw ss e
      else do
        let eInt ← applyCast (.bvToInt sw ss) e
        applyCast (.intToBv tw ts) eInt
    | .int, .nat => pure e
    | .int, .int | .nat, .nat => pure e

/-- Coerce between bitvector widths when both source and target are known. -/
def coerceBvBv (srcInfo? targetInfo? : Option (Nat × Bool)) (e : BExpr) :
    BuildM BExpr := do
  match srcInfo?, targetInfo? with
  | some (sw, ss), some (tw, ts) =>
    if sw == tw && ss == ts then pure e
    else if ss == ts && canPromoteBvWidths sw tw then
      castExprToWiderBvB sw tw ss e
    else do
      let eInt ← applyCast (.bvToInt sw ss) e
      applyCast (.intToBv tw ts) eInt
  | _, _ => pure e

end VerusLean.Boole.Cast
