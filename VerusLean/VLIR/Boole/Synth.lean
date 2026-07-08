/-
  Boole.Synth — builders for the translator's *synthesized* verification aids.

  These are facts the translator injects to re-introduce information that
  Verus's types and iterators guarantee but the `Sequence` lowering drops:
  fixed-size-array lengths, for-range loop index bounds, and the `Seq::map`
  recursion precondition.  This module holds only the pure *shape* of each
  fact.  The *emission sites* stay in `Translate.lean` because they need local
  context (a binder's de Bruijn scope, a struct's fields, or a loop's
  modified-variable set), and each is gated by the corresponding flag in
  `BuildCtx.synthConfig` (`SynthConfig`, in `Context.lean`).  Keeping the
  builders here centralizes "what each fact looks like" so the call sites
  reduce to a guarded one-liner.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Bld

namespace VerusLean.Boole.Synth

open Strata
open Strata.BooleDDM
open StrataDDM (SourceRange)
open VerusLean.Boole.Bld

private def ann (v : α) : StrataDDM.Ann α SourceRange := ⟨default, v⟩
private def noLabel : StrataDDM.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none

/-- `Sequence.length(e) == n` — the fixed-size-array length fact.  Verus's
    compile-time `[T; N]` length is lost when the type lowers to `Sequence T`;
    this re-pins it.  Emitted (under `SynthConfig.fixedArrayLengths`) as
    boundary requires/ensures (including selector-path facts), parameter entry
    `assume`s, mutated-in-loop `invariant`s, and the guarded `<fn>_ret_len`
    axioms.  Never as a global datatype axiom: datatypes are total, so
    `forall s : <dt> :: length(...) == n` would be unsound. -/
def fixedArrayLenFact (e : BExpr) (n : Nat) : BExpr :=
  Bld.eq (Bld.seqLength e) (Bld.intConst (Int.ofNat n))

/-- `Sequence.length(e) <= usize::MAX` — an exec collection's (`Vec<T>`,
    slice) length is a `usize` in Rust, a bound the unbounded `Sequence`
    lowering loses.  Emitted as a parameter entry `assume`; bodies rely on it
    to discharge the increment overflow guards Verus emits for index loops.
    The literal is `2^usizeBitWidth - 1` (`usizeBitWidth = 64`,
    `Coercions.lean`). -/
def seqLenUsizeBoundFact (e : BExpr) : BExpr :=
  Bld.intLe (Bld.seqLength e) (Bld.intConst ((2 : Int) ^ 64 - 1))

/-- `requires 0 <= idx && idx <= Sequence.length(seq)` for a synthesized
    recursion that walks a length-`idx` prefix of `seq` and selects
    `seq[idx-1]` in its step case (the `Seq::map` helper).  The synthesized
    analogue of a hand-written loop's `0 <= i && i <= s.len()` invariant;
    without it the step-case select has no upper bound to discharge its
    out-of-bounds obligation.  Must be built in the recursion's binder scope
    (the `seqE`/`idxE` bvars), which a `recfn_decl`'s spec and body share. -/
def prefixRangeRequires (seqE idxE : BExpr) : BooleDDM.SpecElt SourceRange :=
  let cond := Bld.boolAnd (Bld.intLe (Bld.intConst 0) idxE)
                          (Bld.intLe idxE (Bld.seqLength seqE))
  .requires_spec default noLabel (ann none) cond

/-- The source-level comparison `startExp <= loopVar`: a for-range loop's
    lower-bound invariant.  Verus's `for i in lo..hi` iterator guarantees
    `lo <= i` throughout, but Strata's `for` hands the body only the upper
    bound `i <= hi` (via the guard).  Returned as an `Exp` so the caller lowers
    it through the normal int/bv comparison dispatch and loop-variable scoping
    in `expToBooleFlat`, exactly as for a user-written invariant. -/
def lowerBoundInvExp (startExp : Exp) (loopVarName : String) : Exp :=
  .Binary (.Inequality .Le) startExp (.Var loopVarName)

end VerusLean.Boole.Synth
