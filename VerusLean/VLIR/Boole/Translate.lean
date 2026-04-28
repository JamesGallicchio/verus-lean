/-
  VLIR to BooleDDM Direct Translation

  Translates the Verus-Lean IR (VLIR) directly to BooleDDM AST,
  bypassing the intermediate Strata Core representation.

  This module produces `BExpr`/`BStmt`/`BCmd` nodes from Builder.lean.
  Name-to-index state lives in Boole.Context and is used because BooleDDM
  represents source variables with numeric bvar/fvar indices.
-/

import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Bld
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Cast
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.EnvBuild
import VerusLean.VLIR.Boole.ForLoop
import VerusLean.VLIR.Boole.Inference
import VerusLean.VLIR.Boole.Locals
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Normalize
import VerusLean.VLIR.Boole.Ops
import VerusLean.VLIR.Boole.Projection
import VerusLean.VLIR.Boole.Pruning
import VerusLean.VLIR.Boole.Query
import VerusLean.VLIR.Boole.Reveal
import VerusLean.VLIR.Boole.Signatures
import VerusLean.VLIR.Boole.SupportEmit
import VerusLean.VLIR.Boole.VariantReqs

namespace VerusLean.Boole

namespace Translate

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Cast
open VerusLean.Boole.Coercions
open VerusLean.Boole.Emit
open VerusLean.Boole.EnvBuild
open VerusLean.Boole.ForLoop
open VerusLean.Boole.Inference
open VerusLean.Boole.Locals
open VerusLean.Boole.Names
open VerusLean.Boole.Normalize
open VerusLean.Boole.Ops
open VerusLean.Boole.Projection
open VerusLean.Boole.Pruning
open VerusLean.Boole.Query
open VerusLean.Boole.Reveal
open VerusLean.Boole.Signatures
open VerusLean.Boole.SupportEmit
open VerusLean.Boole.VariantReqs

-- `Boole.Bld` re-exports Builder symbols under a short prefix so Translate
-- can refer to them as `Bld.fvar`, `Bld.app`, etc. without `open`-ing
-- Builder directly (whose names collide with Lean builtins and BooleDDM
-- constructors inside `mutual` blocks).
open VerusLean.Boole.Bld

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩
private def noLabel : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none
private def someLabel (s : String) : Strata.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  ann (some (.label default (ann s)))

/-- Predicate passed to `Normalize.inlineTemps`: which call-function names
    are safe to inline through temp-assignment prefixes without changing
    semantics. This is the translator-side view of library-shape names —
    kept here so `Normalize.lean` stays independent of `Names.lean`. -/
private def isPureBooleBuiltinCallName (fn : Ident) : Bool :=
  isViewName fn || isSeqLenSpecName fn || isVecLenSpecName fn || isVecLenExecName fn
    || isVecIndexSpecName fn || isVecIndexExecName fn
    || isBoxNewName fn || isArrayAsSliceName fn || isSliceIntoVecName fn
    || isCloneExecName fn

/-! ## Environment Helpers -/

def envFromDecls (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := (∅ : VarEnv)) (fun acc (n, t) => acc.insert n t)

private def extendEnv (env : VarEnv) (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := env) (fun acc (n, t) => acc.insert n t)

def boundIndex? (bound : BoundEnv) (name : String) : Option Nat :=
  let rec go (i : Nat) (rest : BoundEnv) : Option Nat :=
    match rest with
    | [] => none
    | (n, _) :: tail => if n == name then some i else go (i + 1) tail
  go 0 bound

private def preludeIdent (name : String) : Ident :=
  .str .anonymous name

private def normalizeCallArgsForCallee (env : VarEnv) (fname : Ident) (args : List Exp) : List Exp :=
  let fnameStr := identToBoole fname
  let argsNoFuel := normalizeCallArgs args
  if hasNoParamFnMarker env fnameStr then
    argsNoFuel.filter (fun e =>
      match e with
      | .Unary (.Box .Int) (.Const (.Int 0) _) => false
      | _ => true)
  else
    argsNoFuel

/-! ## Type Translation -/

/-- Translate a VLIR type to a BooleDDM type. -/
partial def typToBooleType (ty : Typ) : BuildM BType :=
  match ty with
  | .Empty | .Unit => do
    let idx ← resolveFreeVar "Unit"
    pure (fvarTy idx)
  | .Tuple t1 t2 => do
    requireSupport .tuple
    let idx ← resolveFreeVar "Tuple"
    let a1 ← typToBooleType t1
    let a2 ← typToBooleType t2
    pure (fvarTy idx #[a1, a2])
  | .Bool => pure boolTy
  | .Int => pure intTy
  | .Nat => do
    requireSupport .nat
    let idx ← resolveFreeVar "nat"
    pure (fvarTy idx)
  | .UInt w | .SInt w =>
    if isSupportedBvWidth w then pure (bvTy w) else pure intTy
  | .Char => pure intTy
  | .StrSlice => pure strTy
  | .Array t => do
    let elemTy ← typToBooleType t
    pure (mapTy intTy elemTy)
  | .TypParam name => do
    let idx ← resolveFreeVar (sanitizeIdent name)
    pure (fvarTy idx)
  | .SpecFn params ret => do
    let retTy ← typToBooleType ret
    params.foldrM (fun p acc => do
      let pTy ← typToBooleType p
      pure (arrowTy pTy acc)) retTy
  | .Decorated _ inner => typToBooleType inner
  | .Struct name params =>
    -- `vec2seq` branch: translate `Vec<T>` directly to Strata's native
    -- `Sequence T`. This avoids the Vec prelude's view-axioms (expensive
    -- quantifier instantiation for `Vec_view` / `Vec_len` / `Vec_index`)
    -- at the cost of discarding the bounded-length invariant — caller
    -- code must not rely on `Vec_len(v) < 2^64`.
    if isVecTypeName name then
      match params with
      | t :: _ => do pure (seqTy (← typToBooleType t))
      | [] => do pure (seqTy unknownTy)
    else if datatypeNameOf name == "Seq" then
      match params with
      | t :: _ => do pure (seqTy (← typToBooleType t))
      | [] => do pure (seqTy unknownTy)
    else do
      let dtName := datatypeNameOf name
      let idx ← resolveFreeVar dtName
      let args ← params.toArray.mapM typToBooleType
      pure (fvarTy idx args)
  | .Enum name params => do
    let dtName := datatypeNameOf name
    let idx ← resolveFreeVar dtName
    let args ← params.toArray.mapM typToBooleType
    pure (fvarTy idx args)
  | .AirNamed str => do
    let idx ← resolveFreeVar str
    pure (fvarTy idx)

private def typToBooleTypeOrUnknown : Option Typ → BuildM BType
  | some ty => typToBooleType ty
  | none => pure unknownTy

/-! ## Resolve Helpers -/

private def resolveVar (name : String) : BuildM BExpr := do
  let sanName := sanitizeVarName name
  match ← lookupBoundVar sanName with
  | some idx => pure (Bld.bvar idx)
  | none =>
    let idx ← resolveFreeVar sanName
    pure (Bld.fvar idx)

private partial def peelCallWrappers : Exp → Exp
  | .Unary (.Box _) e => peelCallWrappers e
  | .Unary (.Unbox _) e => peelCallWrappers e
  | .MatchBlock _ body => peelCallWrappers body
  | e => e

/-! ## Constant + Type-Args Helpers -/

def constToBoole (expected? : Option Typ) : Const → BExpr
  | .Bool b => boolConst b
  | .Int i =>
    match expected?.bind bitWidthOfTyp with
    | some w => bitvecConstNat w (if i >= 0 then i.toNat else (BitVec.ofInt w i).toNat)
    | none => intConst i
  | .StrSlice s => .strLit default (ann s)
  | .Char c => intConst c.toNat

/-- BooleDDM-emit shim for `Reveal.fnTypeParams` (uses local `ann`). -/
private def mkTypeArgsAnn (params : List String) :
    Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
  if params.isEmpty then
    ann none
  else
    let vars := params.toArray.map fun p =>
      BooleDDM.TypeVar.type_var default (ann p)
    ann (some (BooleDDM.TypeArgs.type_args default (ann vars)))

/-! ## Loop Control Helpers -/

/-- Allocate a fresh synthetic loop label of the form `loop_N`, where `N`
    comes from `BuildCtx.loopLabelCounter`. Used when a `.Loop` has no
    source-level label but its body contains unlabeled `break`/`continue`
    that need a target — deriving the label from AST structure would
    risk collisions between structurally identical loops. -/
private def implicitLoopLabel : BuildM String := do
  let n ← freshLoopLabelId
  pure (sanitizeIdent s!"loop_{n}")

private partial def hasUnlabeledLoopControl : Stm → Bool
  | .BreakOrContinue none _ => true
  | .DeadEnd stm => hasUnlabeledLoopControl stm
  | .If _ b1 b2 =>
    hasUnlabeledLoopControl b1 || (b2.map hasUnlabeledLoopControl).getD false
  | .OpenInvariant stm => hasUnlabeledLoopControl stm
  | .ClosureInner body => hasUnlabeledLoopControl body
  | .AssertQuery _ body => hasUnlabeledLoopControl body
  | .Block stms => stms.any hasUnlabeledLoopControl
  | .Loop .. => false
  | _ => false

partial def bindUnlabeledLoopControlTo (loopLabel : String) : Stm → Stm
  | .BreakOrContinue none isBreak => .BreakOrContinue (some loopLabel) isBreak
  | .DeadEnd stm => .DeadEnd (bindUnlabeledLoopControlTo loopLabel stm)
  | .If cond b1 b2 =>
    .If cond (bindUnlabeledLoopControlTo loopLabel b1) (b2.map (bindUnlabeledLoopControlTo loopLabel))
  | .OpenInvariant stm => .OpenInvariant (bindUnlabeledLoopControlTo loopLabel stm)
  | .ClosureInner body => .ClosureInner (bindUnlabeledLoopControlTo loopLabel body)
  | .AssertQuery mode body => .AssertQuery mode (bindUnlabeledLoopControlTo loopLabel body)
  | .Block stms => .Block (stms.map (bindUnlabeledLoopControlTo loopLabel))
  | s@(.Loop ..) => s
  | s => s

/-! ## Expression Translation -/

private partial def exprHonorsExpectedInt : Exp → Bool
  | .Var _ => true
  | .Const _ _ => true
  | .Binary (.Arith _ _) _ _ => true
  | .Unary (.Box _) e => exprHonorsExpectedInt e
  | .Unary (.Unbox _) e => exprHonorsExpectedInt e
  | .Unary .Trigger e => exprHonorsExpectedInt e
  | .Unary (.HasType _) e => exprHonorsExpectedInt e
  | .Unary .Old e => exprHonorsExpectedInt e
  | .If _ t f => exprHonorsExpectedInt t && exprHonorsExpectedInt f
  | .Bind _ body => exprHonorsExpectedInt body
  | .MatchBlock _ body => exprHonorsExpectedInt body
  | .Call fn _ _ =>
    let name := CallFun.name fn
    isSeqLenSpecName name || isVecLenSpecName name || isVecLenExecName name
  | _ => false

mutual

private partial def comparisonPrelude
    (env : VarEnv) (bound : BoundEnv) (lhs rhs : Exp) :
    BuildM (Option Typ × BExpr × BExpr) := do
  let lhsInfo? := inferComparisonBitInfo env bound lhs
  let rhsInfo? := inferComparisonBitInfo env bound rhs
  let lhsNum? := inferComparisonNumKind env bound lhs
  let rhsNum? := inferComparisonNumKind env bound rhs
  -- `chooseBitArgTyForCmp` only keeps a comparison in bv space when both
  -- operands are naturally bv-shaped, or when the non-bv side is a constant
  -- expression that fits the chosen width. Non-constant mathematical
  -- `int`/`nat` terms fall through to `fallbackToInt`.
  let argTy? := chooseBitArgTyForCmp lhs rhs lhsInfo? rhsInfo?
  let fallbackToInt := argTy?.isNone &&
    (lhsInfo?.isSome || rhsInfo?.isSome ||
     lhsNum? == some .nat || rhsNum? == some .nat)
  if fallbackToInt then
    -- Pass `expected = some .Int` so operands (e.g. `n + 1` with
    -- `n : usize`) emit int arithmetic instead of bv arithmetic that
    -- subsequently overflows under a `bv*_to_int_u` wrap. The post-coerce
    -- is a safety net for shapes that don't honor `expected` (e.g. generic
    -- Calls); skipped for shapes we know honor it, to avoid double-wrap.
    let l0 ← expToBoole env bound (some Typ.Int) lhs
    let r0 ← expToBoole env bound (some Typ.Int) rhs
    let l ← if exprHonorsExpectedInt lhs then pure l0
            else coerceNumeric lhsNum? (some .int) l0
    let r ← if exprHonorsExpectedInt rhs then pure r0
            else coerceNumeric rhsNum? (some .int) r0
    return (argTy?, l, r)
  else
    -- Same narrow-then-widen gating as `.Binary` (see that site).
    let lExpected? := if lhsInfo?.isSome then none else argTy?
    let rExpected? := if rhsInfo?.isSome then none else argTy?
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let targetInfo? := argTy?.bind bitInfoOfTyp
    let l ← coerceBvBv lhsInfo? targetInfo? l0
    let r ← coerceBvBv rhsInfo? targetInfo? r0
    return (argTy?, l, r)

/-- Translate a VLIR expression to a BooleDDM expression. -/
partial def expToBoole (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) :
    Exp → BuildM BExpr
  | .Var x => do
    let actualTy? := boundType? bound x <|> env.get? x
    let e ← resolveVar x
    let srcKind? := actualTy?.bind numKindOfTyp?
    let tgtKind? := expected?.bind numKindOfTyp?
    coerceNumeric srcKind? tgtKind? e
  | .Const c ty =>
    -- Caller-provided `expected?` wins (it knows the surrounding context,
    -- e.g. a shift-amount that must match the LHS width even when the
    -- literal's source typ is narrower). Fall back to the Const's own
    -- VLIR typ when it pins down a bv width — this preserves
    -- source-declared widths (e.g. `1u32`) in contexts where `expected?`
    -- couldn't propagate, such as inside a `.Binary` whose own type
    -- inference was inconclusive (mixed-sign operands).
    let effectiveTy? :=
      expected? <|>
        (if (bitWidthOfTyp ty).isSome then some ty else none)
    return constToBoole effectiveTy? c
  | .StructCtor dt fields => do
    let ctorIdx ← resolveFreeVar (structCtorNameOf dt)
    let ctor := Bld.fvar ctorIdx
    let args ← fields.mapM (fun (field, e) => do
      let fieldExpected? :=
        if isRangeTypeName dt || isRangeCtorFields fields then
          rangeIndexTypFromExpected? expected? <|>
            firstStructParamFromExpected? expected? <|>
            structFieldExpectedType? env dt field
        else
          structFieldExpectedType? env dt field
      expToBoole env bound fieldExpected? e)
    return Bld.appN ctor args
  | .EnumCtor dt variant data => do
    let ctorIdx ← resolveFreeVar (enumCtorNameOf dt variant)
    let ctor := Bld.fvar ctorIdx
    let args ← data.mapM (fun (field, e) =>
      expToBoole env bound (enumFieldExpectedType? env dt variant field) e)
    return Bld.appN ctor args
  | .TupleCtor size data => do
    if size == 2 then requireSupport .tuple
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let ctor := Bld.fvar ctorIdx
    let args ← data.mapM (expToBoole env bound none)
    return Bld.appN ctor args
  | .Binary (.ExtEq deep ty) lhs rhs => do
    extEqExpToBoole env bound deep ty lhs rhs
  | .Binary (.Eq _) lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    let argTy ← typToBooleTypeOrUnknown argTy?
    return Bld.eqTyped argTy l r
  | .Binary .Ne lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    let argTy ← typToBooleTypeOrUnknown argTy?
    return Bld.neqTyped argTy l r
  | .Binary .Xor lhs rhs => do
    let l ← expToBoole env bound none lhs
    let r ← expToBoole env bound none rhs
    return boolNot (boolEquiv l r)
  | .Binary (.Inequality cmp) lhs rhs => do
    let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
    match argTy? with
    | some ty =>
      match bitInfoOfTyp ty with
      | some (w, signed) =>
        let opName := match cmp with
          | .Le => if signed then "SLe" else "ULe"
          | .Lt => if signed then "SLt" else "ULt"
          | .Ge => if signed then "SGe" else "UGe"
          | .Gt => if signed then "SGt" else "UGt"
        match applyBvCmpOp w opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        throw s!"internal error: expected bitvector comparison type, got {repr ty}"
    | none =>
      match cmp with
      | .Le => return intLe l r
      | .Lt => return intLt l r
      | .Ge => return intGe l r
      | .Gt => return intGt l r
  | .Binary op lhs rhs => do
    -- Run arith in `int` when the context demands int or any subtree
    -- mixes int and bv operands. Otherwise bv overflow corrupts the
    -- post-hoc `bv*_to_int_u` wrap (`n == 2^64 - 1` ↦ `bv64_to_int_u(n
    -- + 1bv64) == 0`).
    let arithRunsInInt :=
      match op with
      | .Arith _ _ =>
        expected?.bind numKindOfTyp? == some NumKind.int ||
        expHasMixedIntBvArith env bound (.Binary op lhs rhs)
      | _ => false
    if arithRunsInInt then
      let l ← expToBoole env bound (some Typ.Int) lhs
      let r ← expToBoole env bound (some Typ.Int) rhs
      match applyBinaryOp op l r with
      | some result =>
        let targetKind? := expected?.bind numKindOfTyp?
        let result ← coerceNumeric (some .int) targetKind? result
        return result
      | none => throw s!"unsupported int-context binary op: {repr op}"
    let lhsInfo? := inferBitInfo env bound lhs
    let rhsInfo? := inferBitInfo env bound rhs
    let hasMixedSignedBitArgs :=
      match lhsInfo?, rhsInfo? with
      | some (_, s1), some (_, s2) => s1 != s2
      | _, _ => false
    let baseInfo? :=
      match lhsInfo?, rhsInfo? with
      | some i1, some i2 => chooseBitPromotionInfo? i1 i2
      | some info, none => some info
      | none, some info => some info
      | none, none => none
    let info? :=
      match baseInfo?, expected?.bind bitInfoOfTyp with
      | some (bw, bs), some (ew, es) =>
        if bs == es && canPromoteBvWidths bw ew then some (ew, es) else some (bw, bs)
      | some b, none => some b
      | none, some e =>
        if hasMixedSignedBitArgs then none else some e
      | none, none => none
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    -- Preserve narrow-then-widen for Verus's bit-vector proof mode: only
    -- push `argTy?` when the operand has no natural bv width of its own
    -- (e.g. a literal). See `bitvector_basic::test10` for the failure mode.
    let lExpected? := if lhsInfo?.isSome then none else argTy?
    let rExpected? := if rhsInfo?.isSome then none else argTy?
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let l ← coerceBvBv lhsInfo? info? l0
    let r ← coerceBvBv rhsInfo? info? r0
    match op with
    | .Bitwise bitop _ =>
      let w? := match bitop with
        | .Shl w _ | .Shr w => some w
        | _ => info?.map Prod.fst
      let signed := info?.map Prod.snd |>.getD false
      let opName := match bitop with
        | .BitAnd => "And"
        | .BitOr => "Or"
        | .BitXor => "Xor"
        | .Shl _ _ => "Shl"
        | .Shr _ => if signed then "SShr" else "UShr"
      let resolvedW := w?.getD usizeBitWidth
      match opName with
      | "SShr" =>
        -- Signed shift right: no direct builder, fall through to fvar
        let fnIdx ← resolveFreeVar s!"Bv{resolvedW}.SShr"
        return Bld.appN (Bld.fvar fnIdx) [l, r]
      | _ =>
        match applyBvBitOp resolvedW opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {resolvedW} for op {opName}"
    | .Arith a _ =>
      match info? with
      | some (w, signed) =>
        let opName := match a with
          | .Add => "Add"
          | .Sub => "Sub"
          | .Mul => "Mul"
          | .EuclideanDiv => if signed then "SDiv" else "UDiv"
          | .EuclideanMod => if signed then "SMod" else "UMod"
        match applyBvBinOp w opName l r with
        | some result => return result
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        match applyBinaryOp op l r with
        | some result => return result
        | none => throw s!"unsupported binary op: {repr op}"
    | _ =>
      match applyBinaryOp op l r with
      | some result => return result
      | none => throw s!"unsupported binary op: {repr op}"
  | .Unary op e => do
    let x ←
      match op with
      | .Clip (.U w) _ =>
        let targetW := w.toNat
        let innerInfo? := inferBitInfo env bound e
        let isWidening := match innerInfo? with
          | some (iw, _) => decide (iw < targetW) | none => false
        let hint? := if isWidening then
          innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
        else
          some (.UInt targetW)
        let x0 ← expToBoole env bound hint? e
        if isSupportedBvWidth targetW then
          coerceBvBv innerInfo? (some (targetW, false)) x0
        else
          pure x0
      | .Clip (.I w) _ =>
        let targetW := w.toNat
        let innerInfo? := inferBitInfo env bound e
        let isWidening := match innerInfo? with
          | some (iw, _) => decide (iw < targetW) | none => false
        let hint? := if isWidening then
          innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
        else
          some (.SInt targetW)
        let x0 ← expToBoole env bound hint? e
        if isSupportedBvWidth targetW then
          coerceBvBv innerInfo? (some (targetW, true)) x0
        else
          pure x0
      | .Clip .Nat _ =>
        expToBoole env bound (some .Nat) e
      | .Box t => do
        let inner ← expToBoole env bound (some t) e
        let srcKind? := numKindOfTyp? t
        let tgtKind? := expected?.bind numKindOfTyp?
        coerceNumeric srcKind? tgtKind? inner
      | .BitNot w? =>
        let srcInfo? := inferBitInfo env bound e
        let annotFallback := w?.bind (fun w0 =>
          if isSupportedBvWidth w0 then some (w0, false) else none)
        let targetInfo? := expected?.bind bitInfoOfTyp <|> srcInfo? <|> annotFallback
        let innerExpected? :=
          if srcInfo?.isSome then none
          else targetInfo?.map (fun (w, signed) => bitTypOfInfo w signed)
        expToBoole env bound innerExpected? e
      | _ => expToBoole env bound expected? e
    match op with
    | .Clip _ _ => return x
    | .BitNot w? =>
      let srcInfo? := inferBitInfo env bound e
      let annotFallback := w?.bind (fun w0 =>
        if isSupportedBvWidth w0 then some (w0, false) else none)
      let targetInfo? := expected?.bind bitInfoOfTyp <|> srcInfo? <|> annotFallback
      match targetInfo?.map Prod.fst with
      | some w =>
        let x' ← coerceBvBv srcInfo? targetInfo? x
        return bvNot w x'
      | none => throw "missing bitvector width for op Not"
    | .Old =>
      -- Strata's `old` refers to a pre-state snapshot registered via
      -- `modifies` clauses — we don't emit those, and doing so correctly
      -- would need a wider redesign. Fortunately stripping `.Old` at
      -- emission is semantics-preserving for our pipeline:
      --   • Owned params are immutable in Boole, so `old(p) == p`.
      --   • `&mut` params are modeled via an explicit `_out` rename on the
      --     ensures (see `execFnToBoole`); `substExp` deliberately does not
      --     recurse into `.Unary .Old` bodies (see `Normalize.substExp`),
      --     so the name inside `.Old` keeps pointing at the original input
      --     — i.e. the pre-state value.
      -- In both cases the correct Boole expression is the inner one.
      return x
    | .Trigger => return x
    | .Box _ => return x
    | .Unbox _ => return x
    | .HasType _ => return x
    | .Proj dt variant field _getVariant check => do
      if check == .Yes then
        throw s!"unsupported checked field projection: {dt}::{variant}.{field}"
      let projField := projFieldNameOf dt variant field
      let projIdx ← resolveFreeVar (datatypeDestructorNameOf dt projField)
      return Bld.app (Bld.fvar projIdx) x
    | .IsVariant dt variant => do
      let testerIdx ← resolveFreeVar (enumTesterNameOf dt variant)
      return Bld.app (Bld.fvar testerIdx) x
    | .Proj' size field => do
      let projName ←
        if size == 2 then do
          requireSupport .tuple
          pure s!"Tuple.._{field}"
        else
          pure s!"Tuple_{size}_{field}"
      let projIdx ← resolveFreeVar projName
      return Bld.app (Bld.fvar projIdx) x
    | _ =>
      match applyUnaryOp op x with
      | some result => return result
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToBoole env bound (some .Bool) c
    let t' ← expToBoole env bound expected? t
    let e' ← expToBoole env bound expected? e
    let resultTy ← typToBooleTypeOrUnknown expected?
    return Bld.iteTyped resultTy c' t' e'
  | .Call fn _typs args => do
    let fname := CallFun.name fn
    let fnameStr := identToBoole fname
    let argsFiltered := normalizeCallArgsForCallee env fname args
    -- Seq built-in helper
    let mkSeqBuiltinCall (opName : String) (argSpecs : List (Exp × Option Typ)) := do
      let args' ← argSpecs.mapM (fun (arg, ty?) => expToBoole env bound ty? arg)
      let fnIdx ← resolveFreeVar s!"Sequence.{opName}"
      return Bld.appN (Bld.fvar fnIdx) args'
    let mkFallback := do
      -- Some library fns have abstract declarations emitted as
      -- support decls (not in the prelude text) because their types
      -- reference other support decls. Register the need here so the
      -- declaration appears in the final program.
      if fnameStr == "Seq_lib_zip_with" then
        requireSupport .seqZipWith
      let args' ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
        let paramTy? := lookupFnParamTypeFull env fnameStr idx
        let argExpected? := paramTy? <|> (match expected? with
          | some ty => if isIntTyp ty then some Typ.Int else none
          | none => none)
        expToBoole env bound argExpected? arg)
      let fnIdx ← resolveFreeVar fnameStr
      return Bld.appN (Bld.fvar fnIdx) args'
    -- `vec2seq` branch: `Vec` is translated as `Sequence`, so the
    -- surface-level `view(v)` / `.len()` / `[i]` operations collapse
    -- directly to Strata's built-in Sequence operations. This skips
    -- the Vec prelude entirely, avoiding the expensive view-axiom
    -- quantifier instantiation.
    if isClonedName fname then
      -- Verus's `vstd::prelude::cloned(x, y)` is a ghost predicate
      -- asserting that `y` is a clone of `x`. For every `Clone` impl
      -- Verus accepts, cloning is deterministic, so the predicate
      -- reduces to plain equality. Rewriting at translation time
      -- avoids emitting an uninterpreted `Pervasive_cloned` fvar that
      -- Strata would then flag as "Unknown variable".
      match argsFiltered with
      | [xArg, yArg] =>
        let x ← expToBoole env bound none xArg
        let y ← expToBoole env bound none yArg
        return Bld.eq x y
      | _ => mkFallback
    else if isBoxNewName fname || isArrayAsSliceName fname || isSliceIntoVecName fname
        || isCloneExecName fname then
      match argsFiltered with
      | [arg] => expToBoole env bound expected? arg
      | _ => mkFallback
    else if isViewName fname then
      match argsFiltered with
      | [arg] =>
        match vecVarFromExp arg with
        | some _base =>
          match env.get? _base |>.bind vecElemTyp? with
          | some _ =>
            -- `view(v : Vec<T>)` is identity when Vec := Sequence.
            expToBoole env bound expected? arg
          | none => expToBoole env bound expected? arg
        | none =>
          match expected? with
          | some ty =>
            if isSeqTyp ty then
              match arrayLiteralElemsFromViewArg? arg with
              | some elems => expToBoole env bound expected? (.ArrayLiteral elems)
              | none => expToBoole env bound expected? arg
            else expToBoole env bound expected? arg
          | none => expToBoole env bound expected? arg
      | _ => mkFallback
    else if isSeqLenSpecName fname || isVecLenSpecName fname || isVecLenExecName fname then
      -- Length operations all lower to `Sequence.length(...)`, an int.
      -- The leaf default is `int`; we coerce only when the surrounding
      -- context demands a specific non-int numeric type.  This avoids
      -- needless `int_to_bv64_u` round-trips at comparison sites where
      -- both operands are int-friendly.  `Vec::len()` may receive a
      -- `view(v)` argument that needs unwrapping; `Seq::len()` does not.
      match argsFiltered with
      | [arg] =>
        let arg' := if isSeqLenSpecName fname then arg else unwrapViewCall arg
        let seqExpr ← expToBoole env bound none arg'
        let intLen := seqLength seqExpr
        match expected?.bind numKindOfTyp? with
        | some .nat => coerceNumeric (some .int) (some .nat) intLen
        | some (.bv w s) => coerceNumeric (some .int) (some (.bv w s)) intLen
        | _ => pure intLen
      | _ => mkFallback
    else if isVecIndexSpecName fname || isVecIndexExecName fname then
      -- `v[i]` → `Sequence.select(v, i_as_int)`. Strata's
      -- `Sequence.select` is indexed by `int`, so the usize-typed `i`
      -- is first coerced from bv to int.
      match argsFiltered with
      | [vArg, iArg] =>
        let seqExpr ← expToBoole env bound none (unwrapViewCall vArg)
        let rawIdx ← expToBoole env bound none iArg
        let intIdx ← coerceNumeric (inferNumKind env bound iArg) (some .int) rawIdx
        let selectIdx ← resolveFreeVar "Sequence.select"
        return Bld.appN (Bld.fvar selectIdx) [seqExpr, intIdx]
      | _ => mkFallback
    else if fnameStr == "Seq_index" then
      match argsFiltered with
      | [sArg, iArg] =>
        mkSeqBuiltinCall "select"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (iArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_first" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let zero := intConst 0
        let selectIdx ← resolveFreeVar "Sequence.select"
        return Bld.appN (Bld.fvar selectIdx) [s, zero]
      | _ => mkFallback
    else if fnameStr == "Seq_last" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let one := intConst 1
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.select"))
          [s, intSub (seqLength s) one]
      | _ => mkFallback
    else if fnameStr == "Seq_empty" then do
      let fnIdx ← resolveFreeVar "Sequence.empty"
      return Bld.fvar fnIdx
    else if fnameStr == "Seq_update" then
      match argsFiltered with
      | [sArg, iArg, vArg] =>
        mkSeqBuiltinCall "update"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (iArg, some .Int),
           (vArg, lookupFnParamTypeFull env fnameStr 2)]
      | _ => mkFallback
    else if fnameStr == "Seq_push" then
      match argsFiltered with
      | [sArg, vArg] =>
        mkSeqBuiltinCall "build"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (vArg, lookupFnParamTypeFull env fnameStr 1)]
      | _ => mkFallback
    else if fnameStr == "Seq_take" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "take"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_skip" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "drop"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_add" then
      match argsFiltered with
      | [s1Arg, s2Arg] =>
        let seqTy? := lookupFnParamTypeFull env fnameStr 0
        mkSeqBuiltinCall "append" [(s1Arg, seqTy?), (s2Arg, seqTy?)]
      | _ => mkFallback
    else if fnameStr == "Seq_subrange" then
      match argsFiltered with
      | [sArg, startArg, endArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let start ← expToBoole env bound (some .Int) startArg
        let stop ← expToBoole env bound (some .Int) endArg
        let len := intSub stop start
        let dropped := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.drop")) [s, start]
        let taken := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [dropped, len]
        return taken
      | _ => mkFallback
    else if fnameStr == "Seq_lib_contains" then
      match argsFiltered with
      | [sArg, vArg] =>
        mkSeqBuiltinCall "contains"
          [(sArg, lookupFnParamTypeFull env fnameStr 0),
           (vArg, lookupFnParamTypeFull env fnameStr 1)]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_drop_last" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let one := intConst 1
        let lenMinusOne := intSub (seqLength s) one
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, lenMinusOne]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_remove" then
      match argsFiltered with
      | [sArg, iArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let i ← expToBoole env bound (some .Int) iArg
        let one := intConst 1
        let suffixStart := intAdd i one
        let prefixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, i]
        let suffixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.drop")) [s, suffixStart]
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.append")) [prefixSeq, suffixSeq]
      | _ => mkFallback
    else
      mkFallback
  | .CallLambda body args => do
    let fnExpr ← expToBoole env bound none body
    let args' ← args.mapM (expToBoole env bound none)
    return Bld.appN fnExpr args'
  | .Bind bind body =>
    match bind with
    | .Let v ty rhs =>
      let rhs' :=
        match rhs with
        | .ArrayLiteral elems =>
          if isSeqTyp ty then mkSeqLiteralExp elems else rhs
        | _ => rhs
      let body' := substExp v rhs' body
      expToBoole env bound expected? body'
    | .Quant q vars _trigs => do
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray
        expToBoole env (vars.reverse ++ bound) (some .Bool) body
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      match q with
      | .Forall => return forallExpr binds body'
      | .Exists => return existsExpr binds body'
    | .Lambda vars => do
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray
        expToBoole env (vars.reverse ++ bound) none body
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      return lambdaExpr binds body'
  | .MatchBlock _scrut body =>
    expToBoole env bound expected? body
  | .ArrayLiteral elems => do
    let elemExpected? :=
      if expected?.map isSeqTyp |>.getD false then
        firstStructParamFromExpected? expected?
      else
        none
    let args ← elems.mapM (expToBoole env bound elemExpected?)
    if expected?.map isSeqTyp |>.getD false then
      -- Lower `seq![a, b, c]` to Sequence.empty/Sequence.build chain
      let seqEmptyIdx ← resolveFreeVar "Sequence.empty"
      let seqBuildIdx ← resolveFreeVar "Sequence.build"
      return args.foldl (init := Bld.fvar seqEmptyIdx) (fun acc arg =>
        Bld.appN (Bld.fvar seqBuildIdx) [acc, arg])
    else do
      let litIdx ← resolveFreeVar s!"Array_literal_{elems.length}"
      return Bld.appN (Bld.fvar litIdx) args

private partial def extEqExpToBoole
    (env : VarEnv) (bound : BoundEnv)
    (_deep : Bool) (ty : Typ)
    (lhs rhs : Exp) : BuildM BExpr := do
  let lhs' ← expToBoole env bound (some ty) lhs
  let rhs' ← expToBoole env bound (some ty) rhs
  -- Simplified: use plain equality for all types
  -- Full version would do pointwise comparison for sequences/sets/maps
  return Bld.eqTyped (← typToBooleType ty) lhs' rhs'

end

abbrev expToBooleFlat (env : VarEnv) (expected? : Option Typ) (e : Exp) :
    BuildM BExpr :=
  expToBoole env [] expected? e

/-! ## Statement Translation -/

private def mkQueryObligation (env : VarEnv) (label : String) (requires ensures : List Exp) :
    BuildM (List BStmt) := do
  let reqs ← requires.mapM (expToBooleFlat env (some .Bool))
  let enss ← ensures.mapM (expToBooleFlat env (some .Bool))
  let ensConj := match enss with
    | [] => boolConst true
    | e :: rest => rest.foldl boolAnd e
  let reqs' := reqs.filter (fun e => match e with | .btrue _ => false | _ => true)
  let obligation :=
    if reqs'.isEmpty then ensConj
    else
      let reqConj := match reqs' with
        | [] => boolConst true
        | e :: rest => rest.foldl boolAnd e
      boolImplies reqConj ensConj
  -- Skip vacuous obligations: `assert [label]: true;` proves nothing and
  -- only adds noise. This fires e.g. when Verus pre-computes the asserted
  -- expression to `true` before our `bitvector_query` / `nonlinear_query`
  -- emission, leaving an empty ensures list.
  match obligation with
  | .btrue _ => return []
  | _ => return [assertStmt label obligation]

/-! ## Projected Assignment — BuildM-bound consumers of `Projection.lean` -/

private def lvalueReadExprToBoole (env : VarEnv) (lv : LValue) : BuildM BExpr :=
  expToBooleFlat env none (lvalueToExp lv)

private partial def lowerProjectedAssignRhsToRoot
    (env : VarEnv) (projLayouts : List ProjLayout) :
    LValue → BExpr → BuildM (String × BExpr)
  | .Var name, rhs => pure (name, rhs)
  | .Proj base dt variant field _getVariant check, rhs => do
    if check == .Yes then
      throw s!"unsupported checked projection assignment: {dt}::{variant}.{field}"
    let container ← lvalueReadExprToBoole env base
    let some layout := findProjLayout? projLayouts dt variant
      | throw s!"missing projection layout for {dt}::{variant}.{field}"
    let some targetField := resolveProjFieldName? layout dt variant field
      | throw s!"could not resolve projection field `{field}` in `{dt}::{variant}`"
    if !layout.fields.contains targetField then
      throw s!"projection field `{targetField}` not found in datatype"
    let ctorIdx ← resolveFreeVar layout.ctorName
    let args ← layout.fields.mapM (fun fieldName => do
      if fieldName == targetField then
        pure rhs
      else do
        let projIdx ← resolveFreeVar (datatypeDestructorNameOf dt fieldName)
        pure (Bld.app (Bld.fvar projIdx) container))
    let updatedContainer := Bld.appN (Bld.fvar ctorIdx) args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer
  | .Proj' base size field, rhs => do
    let container ← lvalueReadExprToBoole env base
    if size == 2 then requireSupport .tuple
    let ctorIdx ← resolveFreeVar s!"Tuple_ctor_{size}"
    let args ← (List.range size).mapM (fun i => do
      if i == field then pure rhs
      else do
        let projName :=
          if size == 2 then s!"Tuple.._{i}" else s!"Tuple_{size}_{i}"
        let projIdx ← resolveFreeVar projName
        pure (Bld.app (Bld.fvar projIdx) container))
    let updatedContainer := Bld.appN (Bld.fvar ctorIdx) args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer

/-! ## Statement Translation Main -/

mutual

partial def stmToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    Stm → BuildM (List BStmt)
  | .Call fn _typArgs args => do
    if isGhostPervasiveCallName fn then
      return []
    if isIndexSetName fn then
      match normalizeCallArgsForCallee env fn args with
      | [containerArg, indexArg, valueArg] =>
        match vecVarFromExp containerArg with
        | some baseName =>
          let some containerTy := env.get? baseName
            | throw s!"missing container type for index_set target {baseName}"
          let seqExpr ← expToBoole env [] (some containerTy) (unwrapViewCall containerArg)
          let rawIdx ← expToBoole env [] none indexArg
          let intIdx ← coerceNumeric (inferNumKind env [] indexArg) (some .int) rawIdx
          let valueExpr ← expToBoole env [] none valueArg
          let updateIdx ← resolveFreeVar "Sequence.update"
          let updated := Bld.appN (Bld.fvar updateIdx) [seqExpr, intIdx, valueExpr]
          let containerTy' ← typToBooleType containerTy
          return [setStmtTyped containerTy' (sanitizeVarName baseName) updated]
        | none =>
          throw "unsupported index_set target without a recoverable base variable"
      | _ =>
        throw "unsupported std_specs::core::index_set call shape"
    -- `vec2seq` branch: Vec_* and Slice_into_vec procedure declarations are
    -- dropped at the decl-filter stage (see `declsToBooleProgram`). Call
    -- sites to those procedures therefore target non-existent names; drop
    -- them here so the emitted Boole has no dangling references. This
    -- sacrifices the procedure's effect — vec mutations no longer update
    -- the LHS — but matches the user's explicit "seq or dropped" policy.
    if isVec2SeqDroppedCalleeName fn then
      return []
    let argsFiltered := normalizeCallArgsForCallee env fn args
    let callee := identToBoole fn
    let argsBoole ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
      let paramTy? := lookupFnParamTypeFull env callee idx
      expToBooleFlat env paramTy? arg)
    -- Compute mutable outputs
    let infos := (mutArgMap.get? callee).getD []
    let mutOuts ← infos.filterMapM (fun info => do
      let i := info.idx
      match (argsFiltered.drop i).head? with
      | none => throw s!"mutable call-arg index {i} out of bounds for {callee}"
      | some arg =>
        match vecVarFromExp arg with
        | some v => pure (some (sanitizeVarName v))
        | none => pure none)
    return [callStmt (mutOuts.toArray) callee (argsBoole.toArray)]
  | .Assert exp | .AssertLean exp => do
    match exp with
    | .Unary (.HasType _) _ => return []
    | _ =>
      let e ← expToBooleFlat env (some .Bool) exp
      return [assertStmt "" e]
  | .AssertBitVector requires ensures =>
    mkQueryObligation env "bitvector_query" requires ensures
  | .AssertQuery mode body =>
    match queryReqEnsFromBody body with
    | some (reqs, enss) =>
      mkQueryObligation env (assertQueryModeLabel mode) reqs enss
    | none =>
      stmToBoole env projLayouts mutArgMap retVar? procName body
  | .AssertCompute exp => do
    let e ← expToBooleFlat env (some .Bool) exp
    return [assertStmt "compute" e]
  | .Assume exp => do
    match exp with
    | .Unary (.HasType _) _ => return []
    | _ =>
      let e ← expToBooleFlat env (some .Bool) exp
      return [assumeStmt "" e]
  | .Assign lhs lhsTy rhs _lhsIsInit => do
    if shouldDropAssignAsForLoopScaffolding lhs then
      return []
    if let some lhsName := lvalueVarName? lhs then
      if let some elems := arrayLiteralElemsFromViewArg? rhs then
        let elemTy? :=
          if isSeqTyp lhsTy then firstStructParamFromExpected? (some lhsTy)
          else vecElemTyp? lhsTy
        if let some elemTy := elemTy? then
          let seqEmptyIdx ← resolveFreeVar "Sequence.empty"
          let seqBuildIdx ← resolveFreeVar "Sequence.build"
          let emptySeq := Bld.fvar seqEmptyIdx
          let elems' ← elems.mapM (expToBoole env [] (some elemTy))
          let rhs' :=
            elems'.foldl (fun acc elem => Bld.appN (Bld.fvar seqBuildIdx) [acc, elem]) emptySeq
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
    let rhsCore := peelCallWrappers rhs
    match rhsCore with
    | .Call fn _typArgs args => do
      let fnName := CallFun.name fn
      if isGhostPervasiveCallName fnName then return []
      if isBoxNewName fnName || isArrayAsSliceName fnName || isSliceIntoVecName fnName
          || isCloneExecName fnName then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      -- `vec2seq` branch: same drop as the bare-call path above. Calls
      -- whose RHS is a Vec_*/Slice_into_vec call are dropped entirely,
      -- leaving the LHS variable at its prior value.
      if isVec2SeqDroppedCalleeName fnName then
        return []
      let argsFiltered := normalizeCallArgsForCallee env fnName args
      let callee := identToBoole fnName
      if isVecFromElemName fnName then
        let argsBoole ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
          let paramTy? := lookupFnParamTypeFull env callee idx
          expToBooleFlat env paramTy? arg)
        match lvalueVarName? lhs with
        | some lhsName =>
          return [callStmt #[sanitizeVarName lhsName] callee argsBoole.toArray]
        | none =>
          let tmpName := sanitizeVarName s!"tmp_proj_call_{callee}"
          let ty' ← typToBooleType lhsTy
          let callS := callStmt #[tmpName] callee argsBoole.toArray
          let tmpExpr ← resolveVar tmpName
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs tmpExpr
          return [varStmt tmpName ty', callS, setStmt (sanitizeVarName rootName) updatedRoot]
      else if (lookupFnRetTypeFull env callee).isSome then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else if isViewName fnName || isSeqLenSpecName fnName
            || isVecLenSpecName fnName || isVecLenExecName fnName
            || isVecIndexSpecName fnName || isVecIndexExecName fnName then
        let rhs' ← expToBooleFlat env (some lhsTy) rhs
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
        | none =>
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
          return [setStmt (sanitizeVarName rootName) updatedRoot]
      else
        let argsBoole ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
          let paramTy? := lookupFnParamTypeFull env callee idx
          expToBooleFlat env paramTy? arg)
        let infos := (mutArgMap.get? callee).getD []
        let mutOuts ← infos.filterMapM (fun info => do
          match (argsFiltered.drop info.idx).head? with
          | none => throw s!"mutable call-arg index {info.idx} out of bounds for {callee}"
          | some arg =>
            match vecVarFromExp arg with
            | some v => pure (some (sanitizeVarName v))
            | none => pure none)
        match lvalueVarName? lhs with
        | some lhsName =>
          let lhsNames := #[sanitizeVarName lhsName] ++ mutOuts.toArray
          return [callStmt lhsNames callee argsBoole.toArray]
        | none =>
          -- Projected l-value: use temporary
          let tmpName := sanitizeVarName s!"tmp_proj_call_{callee}"
          let ty' ← typToBooleType lhsTy
          let lhsNames := #[tmpName] ++ mutOuts.toArray
          let callS := callStmt lhsNames callee argsBoole.toArray
          let tmpExpr ← resolveVar tmpName
          let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs tmpExpr
          return [varStmt tmpName ty', callS, setStmt (sanitizeVarName rootName) updatedRoot]
    | _ => do
      let rhs' ← expToBooleFlat env (some lhsTy) rhs
      match lvalueVarName? lhs with
      | some lhsName =>
        let lhsTy' ← typToBooleType lhsTy
        return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
      | none =>
        let (rootName, updatedRoot) ← lowerProjectedAssignRhsToRoot env projLayouts lhs rhs'
        return [setStmt (sanitizeVarName rootName) updatedRoot]
  | .DeadEnd stm =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | .Return exp => do
    match exp, retVar? with
    | some e, some (retName, retTy) =>
      match e with
      | .EnumCtor _ "tuple%0" [] | .TupleCtor 0 [] | .StructCtor _ [] =>
        return [returnStmt procName]
      | _ =>
        let rhs ← expToBooleFlat env (some retTy) e
        let retTy' ← typToBooleType retTy
        return [setStmtTyped retTy' (sanitizeVarName retName) rhs, returnStmt procName]
    | _, _ => return [returnStmt procName]
  | .BreakOrContinue label isBreak =>
    match label with
    | some l => return [exitStmt (some (sanitizeIdent l))]
    | none =>
      throw s!"unsupported unlabeled {(if isBreak then "break" else "continue")} after loop normalization"
  | .If cond b1 b2 => do
    let c ← expToBooleFlat env (some .Bool) cond
    let thenStms ← stmToBoole env projLayouts mutArgMap retVar? procName b1
    let elseStms ← match b2 with
      | some s => stmToBoole env projLayouts mutArgMap retVar? procName s
      | none => pure []
    return [iteStmt c thenStms.toArray elseStms.toArray]
  | .Loop _isForLoop label cond body invs decrease => do
    -- Source-style for-loop recovery is attempted by `stmListToBoole`
    -- before this fallback. If we get here, lower the VLIR loop as a
    -- while loop.
    -- `Loop.cond` has already been populated upstream by `normalizeBody`'s
    -- `extractLoopGuardFromBody` pass (when the source omitted a cond and
    -- the body opened with a guard prefix), so we just consume it here.
    let loopLabel? ← do
      match label with
      | some l => pure (some (sanitizeIdent l))
      | none =>
        let condNeeds := match cond with | some (s, _) => hasUnlabeledLoopControl s | none => false
        if condNeeds || hasUnlabeledLoopControl body then
          pure (some (← implicitLoopLabel))
        else
          pure none
    let condTempSubsts : List (String × Exp) :=
      match cond with
      | some (Stm.Block stms, _) => (splitAssignPrefix stms).fst
      | some (s, _) => match assignFromPrefix s with | some sub => [sub] | none => []
      | none => []
    let condExpr ←
      match cond with
      | some (_, e) => expToBooleFlat env (some .Bool) (substExps condTempSubsts e)
      | none => pure (boolConst true : BExpr)
    let invExprs ← invs.toArray.mapM (fun inv => expToBooleFlat env (some .Bool) inv.body)
    let measureExpr? ← match decrease with
      | [] => pure none
      | e :: _ => do
        let ce0 ← expToBooleFlat env none e
        let srcKind? := inferNumKind env [] e
        let ce ← coerceNumeric srcKind? (some .int) ce0
        pure (some ce)
    let bodyBound := match loopLabel? with | some l => bindUnlabeledLoopControlTo l body | none => body
    let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? procName bodyBound
    let loopStmt := whileStmt condExpr measureExpr? invExprs bodyStms.toArray
    let stmt := match loopLabel? with | some l => blockStmt l #[loopStmt] | none => loopStmt
    return [stmt]
  | .OpenInvariant stm =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | .ClosureInner body =>
    stmToBoole env projLayouts mutArgMap retVar? procName body
  | .Block stms =>
    stmListToBoole env projLayouts mutArgMap retVar? procName stms
  | .Reveal .. =>
    return []

/--
  Emit a recovered source-style `for` loop.  The VLIR shape matching and
  scaffolding filtering lives in `Boole.ForLoop`; this function only lowers the
  recovered loop plan to BooleDDM.
-/
partial def tryForLoopRecovery (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (retVar? : Option (String × Typ))
    (procName : String)
    (stms : List Stm) : BuildM (Option (List BStmt × List Stm)) := do
  match recoverForLoop? stms with
  | none => pure none
  | some loop => do
    let loopVarTy ← typToBooleType loop.loopVarTy
    let loopVarSan := sanitizeVarName loop.loopVarName
    let startExpr ← expToBooleFlat env (some loop.loopVarTy) loop.startExp
    let endE ← expToBooleFlat env (some loop.loopVarTy) loop.endExp
    let limitExpr ← match bitWidthOfTyp loop.loopVarTy with
      | some w => pure (bvSub w endE (bitvecConstNat w 1))
      | none => pure (intSub endE (intConst 1))
    let (invExprs, measureExpr?, bodyStms) ← withScope do
      pushBoundVar loopVarSan
      let invExprs ← loop.invariants.toArray.mapM (fun inv =>
        expToBooleFlat env (some .Bool) inv.body)
      -- Drop the source-level `decreases` witness. Two reasons this is
      -- total rather than selective:
      --   (1) Strata's `for_to_by` / `for_down_to_by` grammar has no
      --       measure slot (tracked upstream in our
      --       `add-for-loop-measure-clause` branch).
      --   (2) When the Verus source has no explicit `decreases`, Verus
      --       auto-synthesizes one as
      --         `if isSome(Pervasive_ghost_decrease(iter))
      --             then Option_Some_0(...) else Pervasive_arbitrary`.
      --       `Pervasive_ghost_decrease` is not in our prelude, and the
      --       `isGhostPervasiveCallName` filter only fires on statement-
      --       level calls, not inside expressions — so keeping the
      --       expression would emit it as an unknown fvar.
      -- When the grammar slot lands, restore the earlier lowering but
      -- skip clauses whose head is a `Pervasive_ghost_*` call:
      --   loop.decrease.head?.filter (not a ghost-pervasive Exp)
      --     |>.mapM (fun e => expToBooleFlat env none e
      --               >>= coerceNumeric _ (some .int))
      let measureExpr? := none
      let bodyStms ← stmToBoole env projLayouts mutArgMap retVar? procName (Stm.Block loop.userBody)
      pure (invExprs, measureExpr?, bodyStms)
    let loopStmt := forToStmt loopVarSan loopVarTy startExpr limitExpr
      measureExpr? invExprs bodyStms.toArray
    let preBoole ← loop.preStms.mapM (stmToBoole env projLayouts mutArgMap retVar? procName)
    pure (some (preBoole.flatten ++ [loopStmt], loop.postStms))

partial def stmListToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    List Stm → BuildM (List BStmt)
  | stms => do
    -- The body has already been put through `normalizeBody` once at the
    -- entry of `proofFnToBoole` / `execFnToBoole`, so no further inlining,
    -- block-flattening, or compute-proof recovery is needed here.
    let hasForLoop := stms.any fun
      | .Loop true _ _ _ _ _ => true
      | _ => false
    if hasForLoop then
      match ← tryForLoopRecovery env projLayouts mutArgMap retVar? procName stms with
      | some (forStms, postStms) =>
        -- Recurse into stmListToBoole (not stmListToBooleAux) so a
        -- second for-loop later in `postStms` also gets recovery
        -- applied. Going through Aux skipped that check.
        let rest ← stmListToBoole env projLayouts mutArgMap retVar? procName postStms
        return forStms ++ rest
      | none =>
        stmListToBooleAux env projLayouts mutArgMap retVar? procName stms
    else
      stmListToBooleAux env projLayouts mutArgMap retVar? procName stms

partial def stmListToBooleAux (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    List Stm → BuildM (List BStmt)
  | (.BreakOrContinue none true) :: (.Assume (.Const (.Bool false) _)) :: rest => do
    let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName rest
    return [assumeStmt "" (boolConst false)] ++ s2
  | a :: (.Assume e) :: next :: rest =>
    if isAssertAssumeEcho a e then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (a :: next :: rest)
    else if isTrivialTrueAssert a && isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
    else if isTrivialTrueAssert a then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.AssertCompute e) :: next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.Assume e) :: next :: rest)
      return s1 ++ s2
  | (.Assume e) :: next :: rest =>
    if isQueryScaffoldingAssume e next then
      stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
    else do
      let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName (.Assume e)
      let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
      return s1 ++ s2
  | a :: next :: rest =>
    match next with
    | .Assume e =>
      if isAssertAssumeEcho a e then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName (a :: rest)
      else if isTrivialTrueAssert a then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName ((.AssertCompute e) :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
        return s1 ++ s2
    | _ =>
      if isTrivialTrueAssert a && isQueryStmt next then
        stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
      else do
        let s1 ← stmToBoole env projLayouts mutArgMap retVar? procName a
        let s2 ← stmListToBooleAux env projLayouts mutArgMap retVar? procName (next :: rest)
        return s1 ++ s2
  | [stm] =>
    stmToBoole env projLayouts mutArgMap retVar? procName stm
  | [] => return []
end

/-! ## Declaration Translation -/

def typeArgsFromTyps (tys : List Typ) : List String :=
  (tys.flatMap typTypeVars).eraseDups

def typeArgsFromDecls (decls : List (String × Typ)) : List String :=
  typeArgsFromTyps (decls.map Prod.snd)

/-! ### Building BooleDDM Commands -/

private def mkMonoInputs (inputs : List (String × Typ)) :
    BuildM (BooleDDM.Bindings SourceRange × Array String) := do
  let mut bindings : Array (BooleDDM.Binding SourceRange) := #[]
  let mut names : Array String := #[]
  for (name, ty) in inputs do
    let sanName := sanitizeVarName name
    let ty' ← typToBooleType ty
    bindings := bindings.push
      (BooleDDM.Binding.mkBinding default (ann sanName) (BooleDDM.TypeP.expr ty'))
    names := names.push sanName
  pure (BooleDDM.Bindings.mkBindings default (ann bindings), names)

private def mkMonoOutputs (outputs : List (String × Typ)) :
    BuildM (Option (BooleDDM.MonoDeclList SourceRange) × Array String) := do
  if outputs.isEmpty then
    pure (none, #[])
  else
    let first := outputs.head!
    let firstName := sanitizeVarName first.1
    let firstTy ← typToBooleType first.2
    let init := MonoDeclList.monoDeclAtom default
      (MonoBind.mono_bind_mk default (ann firstName) firstTy)
    let (result, names) ← outputs.tail.foldlM (fun (acc, names) (name, ty) => do
      let sanName := sanitizeVarName name
      let ty' ← typToBooleType ty
      pure (MonoDeclList.monoDeclPush default acc
        (MonoBind.mono_bind_mk default (ann sanName) ty'),
        names.push sanName))
      (init, #[firstName])
    pure (some result, names)

private def mkSpecElts (env : VarEnv) (pre post : List Exp) (modifies : List String) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  -- Drop trivial `true` spec clauses/conjuncts without otherwise
  -- reshaping non-trivial `&&` expressions.
  let pre' := pre.flatMap dropTrueConjuncts
  let post' := post.flatMap dropTrueConjuncts
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  for e in pre' do
    let e' ← expToBooleFlat env (some .Bool) e
    elts := elts.push (.requires_spec default noLabel (ann none) e')
  for e in post' do
    let e' ← expToBooleFlat env (some .Bool) e
    elts := elts.push (.ensures_spec default noLabel (ann none) e')
  if !modifies.isEmpty then
    let modNames := modifies.toArray.map (fun n => ann (sanitizeVarName n))
    elts := elts.push (.modifies_spec default (ann modNames))
  pure elts

private def localsToVarStmts (locals : List LocalDeclInfo) : BuildM (List BStmt) := do
  locals.mapM (fun decl => do
    let ty' ← typToBooleType decl.ty
    let sanName := sanitizeVarName decl.name
    pushBoundVar sanName
    pure (varStmt sanName ty'))

/-! ### SpecFn → BCmd -/

/-- Build `requires <dt>..is<variant>(<param>)` SpecElts from `rootExposedProjs`
    output. Assumes the function's input names have already been `addBoundVars`-ed
    in the current scope so the tester argument resolves to a bvar.

    Skips Projs on struct-typed parameters (single-variant datatypes): Strata
    generates no tester for those, and the precondition would be trivially
    true anyway. We detect this by looking up the tester name in the current
    free-variable registry — only multi-variant enum translation
    (`enumToBoole`) registers tester names. -/
private def synthVariantRequires
    (reqs : List (String × Ident × String)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  for (paramName, dt, variant) in reqs do
    let testerName := enumTesterNameOf dt variant
    let ctx ← get
    match ctx.freeVarIndex? testerName with
    | none =>
      -- Tester not registered: the datatype is a struct (one variant) or
      -- this Proj targets a name Strata doesn't recognise. Either way the
      -- precondition is trivial; skip.
      continue
    | some testerIdx =>
      let paramExpr ← resolveVar paramName
      let cond := Bld.app (Bld.fvar testerIdx) paramExpr
      elts := elts.push (.requires_spec default noLabel (ann none) cond)
  pure elts

def specFnToBoole (env : VarEnv) (emitBody : Bool) (f : SpecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let (inputBindings, inputNames) ← mkMonoInputs f.inputs
  let outputTy ← typToBooleType f.returnType
  let envLocal := extendEnv env f.inputs
  let (body?, specElts) ← withScope do
    addBoundVars inputNames
    let body? ← if emitBody then
      match f.body with
      | some b => pure (some (← expToBooleFlat envLocal (some f.returnType) b))
      | none => pure none
    else pure none
    -- Synthesise variant-precondition `requires` for Verus's inline accessor
    -- pattern (`impl&%N::arrow_*` style spec fns whose body is a bare
    -- `.Proj`). See `rootExposedProjs` for the detection rule.
    let inputNameSet := inputNames.toList
    let variantReqs := match f.body with
      | some b =>
        dedupVariantReqs <| (rootExposedProjs b).filter (fun (n, _, _) => inputNameSet.contains n)
      | none => []
    let elts ← synthVariantRequires variantReqs
    pure (body?, elts)
  match body? with
  | some body =>
    if f.isRecursive then
      let recDecl :=
        BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy (ann specElts) body
      pure (.command_recfndefs default (ann #[recDecl]))
    else
      pure (.command_fndef default name typeArgs inputBindings outputTy (ann specElts) body (ann none))
  | none =>
    pure (.command_fndecl default name typeArgs inputBindings outputTy)

/-! ### ProofFn/ExecFn → BCmd -/

def proofFnToBoole (env : VarEnv) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ProofFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let hasRet := match f.returnType with | .Unit | .Empty => false | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let retNames := if hasRet then [f.retName] else []
  let bodyStm? := f.body.map (fun b =>
    let b := expandReveals sfMap b
    let b := stripDecreaseArtifacts b
    let b := normalizeBody isPureBooleBuiltinCallName b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s)
  let setVars := match bodyStm? with | some body => collectSetVars body | none => []
  let bodyHasForLoop := match bodyStm? with | some body => stmHasForLoop body | none => false
  let inputNames := f.inputs.map Prod.fst
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let localsAll := match bodyStm? with
    | some body => filterLocalsByUse (stripForLoopScaffoldingFromBody body) localsAll
    | none => localsAll
  let outputs := retDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.requires f.ensures []
    let localStmts ← localsToVarStmts localsAll
    let retVar? := if hasRet then some (f.retName, f.returnType) else none
    let bodyStmts ← match bodyStm? with
      | some stm => stmToBoole envLocal projLayouts mutArgMap retVar? fnName stm
      -- Body-less proof fn (`#[verifier::external_body]` on `proof fn`):
      -- mirror the exec-fn isDeclOnly arm — emit `assume false;` so the
      -- ensures are trivially satisfied. (Body-less in Strata is *not*
      -- treated as a trusted declaration; see the exec-fn comment.)
      | none => pure [assumeStmt "" (boolConst false)]
    let allStmts := localStmts ++ bodyStmts
    let body := BooleDDM.Block.block default (ann allStmts.toArray)
    pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

private def synthesizeVecFromElemBody (f : ExecFn) : BuildM BBlock := do
  let (elemName, elemTy, nName, nTy) ←
    match f.inputs with
    | (elemName, elemTy) :: (nName, nTy) :: _ => pure (elemName, elemTy, nName, nTy)
    | _ => throw "Vec_from_elem expects element and length inputs"
  let resolveProcVar (name : String) : BuildM BExpr := do
    let idx ← resolveFreeVar (sanitizeVarName name)
    pure (Bld.fvar idx)
  let retTy ← typToBooleType f.returnType
  let elemTy' ← typToBooleType elemTy
  let nTy' ← typToBooleType nTy
  let seqBuildIdx ← resolveFreeVar "Sequence.build"
  let seqEmptyIdx ← resolveFreeVar "Sequence.empty"
  let seqSelectIdx ← resolveFreeVar "Sequence.select"
  let zeroInt := intConst 0
  let zeroBv := bitvecConstNat usizeBitWidth 0
  let oneBv := bitvecConstNat usizeBitWidth 1
  let initEmptyExpr := Bld.fvar seqEmptyIdx
  let initStmt := setStmtTyped retTy (sanitizeVarName f.retName) initEmptyExpr
  let loopVarName := "i"
  let loopStmt ← withScope do
    pushBoundVar loopVarName
    let nExpr ← resolveProcVar nName
    let iExpr ← resolveVar loopVarName
    let elemExpr ← resolveProcVar elemName
    let retExpr ← resolveProcVar f.retName
    let lenExpr ← coerceNumeric (some .int) (some (.bv usizeBitWidth false)) (seqLength retExpr)
    let limitExpr := bvSub usizeBitWidth nExpr oneBv
    let invBounds := boolAnd (bvUle usizeBitWidth zeroBv iExpr) (bvUle usizeBitWidth iExpr nExpr)
    let invLen := eqTyped nTy' lenExpr iExpr
    let invElemsBody ← withScope do
      let quantVarName := "j"
      pushBoundVar quantVarName
      let jExpr ← resolveVar quantVarName
      let jBv ← coerceNumeric (some .int) (some (.bv usizeBitWidth false)) jExpr
      let iExpr ← resolveVar loopVarName
      let elemExpr ← resolveProcVar elemName
      let retExpr ← resolveProcVar f.retName
      let inRange := boolAnd (intLe zeroInt jExpr) (bvUlt usizeBitWidth jBv iExpr)
      let selectExpr := Bld.appN (Bld.fvar seqSelectIdx) [retExpr, jExpr]
      pure (boolImplies inRange (eqTyped elemTy' selectExpr elemExpr))
    let invElems := forallExpr #[("j", intTy)] invElemsBody
    let nextRet := Bld.appN (Bld.fvar seqBuildIdx) [retExpr, elemExpr]
    pure (forToStmt loopVarName nTy' zeroBv limitExpr none #[invBounds, invLen, invElems]
      #[setStmtTyped retTy (sanitizeVarName f.retName) nextRet])
  pure (BooleDDM.Block.block default (ann #[initStmt, loopStmt]))

def execFnToBoole (env : VarEnv) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ExecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let mutOutDecls :=
    f.inputs.filterMap (fun (n, t) =>
      (mutRefPayload? t).map (fun payloadTy => (n, s!"{n}_out", payloadTy)))
  let mutRenames := mutOutDecls.map (fun (n, outName, _) => (n, outName))
  let rewrittenBody :=
    let b := stripDecreaseArtifacts (expandReveals sfMap (applyNameSubstsStm mutRenames f.body))
    let b := normalizeBody isPureBooleBuiltinCallName b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s
  let rewrittenEnsures := f.ensures.map (applyNameSubstsExp mutRenames)
  let hasRet := match f.returnType with | .Unit | .Empty => false | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let mutOutputDecls := mutOutDecls.map (fun (_, outName, payloadTy) => (outName, payloadTy))
  let inputNames := f.inputs.map Prod.fst
  let retNames := (if hasRet then [f.retName] else []) ++ mutOutputDecls.map Prod.fst
  let setVars := collectSetVars rewrittenBody
  let bodyHasForLoop := stmHasForLoop rewrittenBody
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let localsAll := filterLocalsByUse (stripForLoopScaffoldingFromBody rewrittenBody) localsAll
  let outputs := retDecls ++ mutOutputDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let isDeclOnly := match f.body with | .Block [] => true | _ => false
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.requires rewrittenEnsures []
    if isDeclOnly && isVecFromElemName f.name then
      let body ← synthesizeVecFromElemBody f
      pure (specElts, body)
    else if isDeclOnly then
      -- `#[verifier::external]` tells Verus to ignore the given item. Verus
      -- will error if any verified code attempts to reference the given item.
      -- `#[verifier::external_body]` tells Verus to only consider the function
      -- definition but not the function body, trusting that it correctly
      -- satisfies its specification.
      -- Strata's `command_procedure` with `body = none` is *not* treated as
      -- a trusted declaration — it still emits per-ensures obligations that
      -- the (missing) body must satisfy, which fails for non-trivial specs.
      -- Emit `{ assume false; }` instead so the body trivially satisfies its
      -- postconditions; callers continue to use the spec as written.
      let body := BooleDDM.Block.block default (ann #[assumeStmt "" (boolConst false)])
      pure (specElts, body)
    else
      let localStmts ← localsToVarStmts localsAll
      -- Init mutable-out variables from inputs
      let mutOutInits ← mutOutDecls.mapM (fun (inName, outName, payloadTy) => do
        let inExpr ← resolveVar inName
        let outTy ← typToBooleType payloadTy
        pure (setStmtTyped outTy (sanitizeVarName outName) inExpr))
      let retVar? := if hasRet then some (f.retName, f.returnType) else none
      let bodyStmts ← stmToBoole envLocal projLayouts mutArgMap retVar? fnName rewrittenBody
      let allStmts := localStmts ++ mutOutInits ++ bodyStmts
      let body := BooleDDM.Block.block default (ann allStmts.toArray)
      pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

/-! ### Struct/Enum → BCmd -/

def structToBoole (s : Struct) : BuildM BCmd := do
  let dtName := datatypeNameOf s.name
  addFreeVars #[dtName]
  let ctorName := structCtorNameOf s.name
  let testerName := s!"{dtName}..is{ctorName}"
  let fieldNames := s.fields.map (fun (f, _) => fieldAccessorNameOf f)
  addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
  let constrArgs ← if s.fields.isEmpty then
    pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
  else do
    let bindings ← s.fields.toArray.mapM fun (fname, ty) => do
      let ty' ← typToBooleType ty
      pure (BooleDDM.Binding.mkBinding default (ann (fieldAccessorNameOf fname)) (BooleDDM.TypeP.expr ty'))
    pure (ann (some (ann bindings)))
  let constr := BooleDDM.Constructor.constructor_mk default (ann ctorName) constrArgs
  let constrList := BooleDDM.ConstructorList.constructorListAtom default constr
  let typeArgs : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    if s.typeParams.isEmpty then ann none
    else
      let bindings := s.typeParams.toArray.map fun param =>
        BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
      ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
  let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann dtName) typeArgs constrList
  pure (.command_datatypes default (ann #[dtDecl]))

def enumToBoole (e : Enum) : BuildM BCmd := do
  let dtName := datatypeNameOf e.name
  addFreeVars #[dtName]
  if e.fields.isEmpty then
    -- Abstract type
    let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if e.typeParams.isEmpty then ann none
      else
        let bindings := e.typeParams.toArray.map fun param =>
          BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    pure (.command_typedecl default (ann dtName) args)
  else
    -- Register all names
    for field in e.fields do
      match field with
      | .labeled variant data =>
        let ctorName := enumCtorNameOf e.name variant
        let testerName := enumTesterNameOf e.name variant
        let fieldNames := data.map (fun (fname, _) => projFieldNameOf e.name variant fname)
        addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
      | .tuple variant ts =>
        let ctorName := enumCtorNameOf e.name variant
        let testerName := enumTesterNameOf e.name variant
        let fieldNames := (List.range ts.length).map (fun i => projFieldNameOf e.name variant (toString i))
        addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
    let constrs ← e.fields.toArray.mapM fun field => do
      match field with
      | .labeled variant data =>
        let constrArgs ← if data.isEmpty then
          pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
        else do
          let bindings ← data.toArray.mapM fun (fname, ty) => do
            let ty' ← typToBooleType ty
            let fieldName := projFieldNameOf e.name variant fname
            pure (BooleDDM.Binding.mkBinding default (ann fieldName) (BooleDDM.TypeP.expr ty'))
          pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann (enumCtorNameOf e.name variant)) constrArgs)
      | .tuple variant ts =>
        let constrArgs ← if ts.isEmpty then
          pure (ann (none : Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
        else do
          let bindings ← ts.zipIdx.toArray.mapM fun (ty, i) => do
            let ty' ← typToBooleType ty
            let fieldName := projFieldNameOf e.name variant (toString i)
            pure (BooleDDM.Binding.mkBinding default (ann fieldName) (BooleDDM.TypeP.expr ty'))
          pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann (enumCtorNameOf e.name variant)) constrArgs)
    let constrList :=
      if constrs.isEmpty then
        BooleDDM.ConstructorList.constructorListAtom default
          (BooleDDM.Constructor.constructor_mk default (ann "") (ann none))
      else
        constrs[1:].foldl
          (fun acc c => BooleDDM.ConstructorList.constructorListPush default acc c)
          (BooleDDM.ConstructorList.constructorListAtom default constrs[0]!)
    let typeArgs : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
      if e.typeParams.isEmpty then ann none
      else
        let bindings := e.typeParams.toArray.map fun param =>
          BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
        ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
    let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann dtName) typeArgs constrList
    pure (.command_datatypes default (ann #[dtDecl]))

/-! ### FuncCheckSst → BCmd -/

def funcCheckSstToBoole (env : VarEnv) (f : FuncCheckSst) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.decls .Unit)
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.decls
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs []
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env f.decls
  let (specElts, body) ← withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let specElts ← mkSpecElts envLocal f.reqs f.postCondition []
    let body := BooleDDM.Block.block default (ann #[])
    pure (specElts, body)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn spec (ann (some body)))

/-! ### Top-Level Declaration Translation -/

partial def declToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (sfMap : SpecFnMap)
    (allDecls : List Decl) :
    Decl → BuildM (List BCmd)
  | .assertion _ => return []
  | .specFn f => do
    let cmd ← specFnToBoole env (!f.isOpaque) f
    return [cmd]
  | .proofFn f => do
    let cmd ← proofFnToBoole env projLayouts mutArgMap sfMap f
    return [cmd]
  | .execFn f => do
    let cmd ← execFnToBoole env projLayouts mutArgMap sfMap f
    return [cmd]
  | .func f => do
    let cmd ← funcCheckSstToBoole env f
    return [cmd]
  | .struct s => do
    let cmd ← structToBoole s
    return [cmd]
  | .enum e => do
    let cmd ← enumToBoole e
    return [cmd]
  | .mutualBlock ds => do
    -- Separate spec functions from other declarations
    let specFns := ds.filterMap (fun d => match d with | .specFn f => some f | _ => none)
    let others := ds.filter (fun d => match d with | .specFn _ => false | _ => true)
    -- Translate spec functions as a recursive block
    let recCmds ← if specFns.isEmpty then pure []
    else do
      for f in specFns do addFreeVars #[identToBoole f.name]
      let recDecls ← specFns.toArray.mapM fun f => do
        let fnName := identToBoole f.name
        let name := ann fnName
        let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
        let (inputBindings, inputNames) ← mkMonoInputs f.inputs
        let outputTy ← typToBooleType f.returnType
        let envLocal := extendEnv env f.inputs
        let (body, specElts) ← withScope do
          addBoundVars inputNames
          let body ← match f.body with
            | some b => expToBooleFlat envLocal (some f.returnType) b
            | none => pure (boolConst true)
          -- Same variant-precondition synthesis as the non-mutual path.
          let inputNameSet := inputNames.toList
          let variantReqs := match f.body with
            | some b =>
              dedupVariantReqs <|
                (rootExposedProjs b).filter (fun (n, _, _) => inputNameSet.contains n)
            | none => []
          let elts ← synthVariantRequires variantReqs
          pure (body, elts)
        pure (BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy (ann specElts) body)
      pure [BooleDDM.Command.command_recfndefs default (ann recDecls)]
    -- Translate non-spec declarations normally
    let otherCmds ← others.foldlM (fun acc d => do
      let cmds ← declToBoole env projLayouts mutArgMap sfMap allDecls d
      return acc ++ cmds) []
    return recCmds ++ otherCmds

/-! ## Prelude and Entry Point -/

private def buildEnv (decls : List Decl)
    (noParamFns : List String) (sfMap : SpecFnMap) : VarEnv :=
  let inputDecls := decls.flatMap (fun d => match d with
    | .specFn f => f.inputs
    | .proofFn f => f.inputs ++ [(f.retName, f.returnType)] ++ localBindings f.locals
    | .execFn f => f.inputs ++ [(f.retName, f.returnType)] ++ localBindings f.locals
    | .func f => f.decls
    | .struct s => s.fields
    | .enum e => e.fields.flatMap (fun field => match field with
        | .labeled _ data => data
        | .tuple _ ts => ts.zipIdx.map (fun (ty, i) => (s!"_{i}", ty)))
    | _ => [])
  let env := addNoParamFnMarkers (envFromDecls inputDecls) noParamFns
  let env := addFnRetTypes env sfMap
  let env := addAllFnParamTypes env decls
  let env := addDatatypeAccessorRetTypes env decls
  env

/-- Extract the primary name from a VLIR declaration. -/
private def declPrimaryName : Decl → String
  | .assertion a => a.name.toString
  | .specFn f => f.name.toString
  | .proofFn f => f.name.toString
  | .execFn f => f.name.toString
  | .struct s => s.name.toString
  | .enum e => e.name.toString
  | .func f => f.name.toString
  | .mutualBlock ds => match ds with | d :: _ => declPrimaryName d | [] => ""

/-- Check whether a VLIR declaration is purely for-loop iterator scaffolding
    that should be pruned when for-loops are successfully recovered. -/
private def isForLoopScaffoldingDecl (name : String) : Bool :=
  let lower := name.toLower
  -- Iterator next/into_iter procedures
  lower.endsWith "next" && lower.contains "iterator" ||
  lower.endsWith "into_iter" && lower.contains "collect" ||
  -- Ghost pervasive functions (ForLoopGhostIterator, ForLoopGhostIteratorNew)
  lower.contains "pervasive" && (lower.contains "ghost" || lower.contains "forloop") ||
  -- Range datatype (core.ops.range.Range or Ops_Range_range)
  (lower.contains "range" && (lower.contains "ops" || lower.contains "ops_range")) ||
  -- Option datatype (core.option.Option or Option_option)
  (lower.contains "option" && (lower.contains "core" || lower.contains "option_option")) ||
  -- Std specs for iterators (std_specs.range, std_specs.core.iter)
  lower.contains "std_specs" && (lower.contains "iter" || lower.contains "range") ||
  -- RangeGhostIterator
  lower.contains "rangeghost"

/-- Check whether any ExecFn in a declaration list has a for-loop body. -/
private def declsHaveForLoop (decls : List Decl) : Bool :=
  decls.any fun
    | .execFn f => stmHasForLoop f.body
    | .proofFn f => f.body.map stmHasForLoop |>.getD false
    | _ => false

def declsToBooleProgram (decls : List Decl) :
    BuildM (Array BCmd) := do
  -- Drop Verus-synthesised impl-block accessor spec fns that aren't
  -- transitively referenced by any user-level decl. Eager emission of every
  -- `Impl__N_arrow_*` bloats the output and slows verification; most tests
  -- use only a handful.
  let decls := pruneUnreferencedImpls decls
  let noParamFns := collectNoParamFnNamesFromDecls decls
  let projLayouts := buildProjLayouts decls
  let mutArgMap := collectMutArgMapFromDecls decls
  let sfMap := collectSpecFns decls
  let env := buildEnv decls noParamFns sfMap
  -- Detect whether any for-loop will be recovered
  let hasForLoop := declsHaveForLoop decls
  -- `vec2seq` branch: Verus emits stub `proc Vec_*` / `proc Slice_into_vec`
  -- wrappers (and a few other Vec-named procedures) to cover the Rust Vec
  -- surface — `Vec_new`, `Vec_len`, `Vec_push`, `Vec_from_elem`,
  -- `Slice_into_vec`, etc. Since we translate every Vec operation directly
  -- to the corresponding `Sequence.*` op at the call site (see the
  -- `isVecLenSpecName` / `isVecIndexSpecName` / `isViewName` handlers
  -- in `expToBoole`), those stub declarations are never invoked. Their
  -- specs also frequently mix `Map int T` (array) and `Sequence T` in
  -- ways that no longer typecheck under vec2seq. Drop them here so the
  -- output has no residual `Vec`-named symbols.
  let isVec2SeqDroppedDecl (d : Decl) : Bool :=
    -- Match on the sanitized (identToBoole) name, not the raw path, so
    -- `vstd::vec::Vec::len` → `Vec_len` and the prefix check fires.
    -- Also drops procedure decls whose calls are inlined at every call
    -- site (see `isPureBooleBuiltinCallName` / `expToBoole`): the stubs
    -- have no remaining callers and otherwise leak as dead decls.
    match Pruning.declName? d with
    | some n =>
      (n.startsWith "Vec_" && n != "Vec_from_elem")
        || n.startsWith "Slice_into_vec"
        || n == "Clone_Clone_clone"
        || n == "Boxed_box_new"
        || n == "Array_array_as_slice"
    | none => false
  -- When for-loop recovery is active, skip translating iterator scaffolding declarations
  let filteredDecls := decls.filter fun d =>
    let name := declPrimaryName d
    !isVec2SeqDroppedDecl d &&
      !(hasForLoop && isForLoopScaffoldingDecl name)
  -- Translate user declarations first to discover which support names are needed
  let mut userCmds : Array BCmd := #[]
  for d in filteredDecls do
    let cmds ← declToBoole env projLayouts mutArgMap sfMap decls d
    userCmds := userCmds ++ cmds.toArray
  -- Support declarations are emitted from explicit requirements recorded
  -- during lowering, not from incidental free-variable references.
  let ctx ← get
  let supportNeeds := ctx.supportNeeds
  let supportCmds ← supportDeclCommands typToBooleType supportNeeds
  return supportCmds ++ userCmds

/-- Convenience: run the full translation pipeline and return the resulting
    BooleDDM commands, or an error string. -/
def translateDecls (decls : List Decl) : Except String (Array BCmd) :=
  match (declsToBooleProgram decls).run emptyCtx with
  | .ok (cmds, _) => .ok cmds
  | .error e => .error e

/-- Like `translateDecls` but also returns the build context for name resolution. -/
def translateDeclsWithCtx (decls : List Decl) : Except String (Array BCmd × BuildCtx) :=
  match (declsToBooleProgram decls).run emptyCtx with
  | .ok (cmds, ctx) => .ok (cmds, ctx)
  | .error e => .error e

/-- Like `translateDeclsWithCtx` but pre-registers prelude names so fvar
    indices align with Strata's `Program.globalContext` when the prelude is
    prepended to the output. -/
def translateDeclsWithPrelude (decls : List Decl) (preludeNames : Array String) :
    Except String (Array BCmd × BuildCtx) :=
  let initCtx := emptyCtx.addGlobalFreeVars preludeNames
  match (declsToBooleProgram decls).run initCtx with
  | .ok (cmds, ctx) => .ok (cmds, ctx)
  | .error e => .error e

/-- Extract the declared name from a BooleDDM command, if it has one. -/
def cmdDeclName? : BCmd → Option String
  | .command_fndecl _ name _ _ _ => some name.val
  | .command_fndef _ name _ _ _ _ _ _ => some name.val
  | .command_recfndefs _ _ => none  -- multiple names
  | .command_typedecl _ name _ => some name.val
  | .command_typesynonym _ name _ _ _ => some name.val
  | .command_datatypes _ _ => none  -- multiple names
  | .boole_procedure _ name _ _ _ _ _ => some name.val
  | .command_procedure _ name _ _ _ _ => some name.val
  | .command_axiom _ _ _ => none
  | .command_var _ bind => some (match bind with | .bind_mk _ name _ _ => name.val)
  | .command_distinct _ _ _ => none
  | .command_constdecl _ name _ _ => some name.val
  | .command_block _ _ => none

end Translate

end VerusLean.Boole
