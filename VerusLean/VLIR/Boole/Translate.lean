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
import VerusLean.VLIR.Boole.IntPromotion
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
import VerusLean.VLIR.Boole.TraitResolve
import VerusLean.VLIR.Boole.Synth
import VerusLean.VLIR.Boole.VariantReqs

namespace VerusLean.Boole

namespace Translate

open Strata
open Strata.BooleDDM
open StrataDDM (SourceRange)
open VerusLean.Boole.Cast
open VerusLean.Boole.Coercions
open VerusLean.Boole.Context
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

private def ann (v : α) : StrataDDM.Ann α SourceRange := ⟨default, v⟩
private def noLabel : StrataDDM.Ann (Option (BooleDDM.Label SourceRange)) SourceRange := ann none
private def someLabel (s : String) : StrataDDM.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  ann (some (.label default (ann s)))

/-- Predicate passed to `Normalize.inlineTemps`: which call-function names
    are safe to inline through temp-assignment prefixes without changing
    semantics. This is the translator-side view of library-shape names —
    kept here so `Normalize.lean` stays independent of `Names.lean`. -/
private def isPureBooleBuiltinCallName (fn : Ident) : Bool :=
  isViewName fn || isSeqLenSpecName fn || isVecLenSpecName fn || isVecLenExecName fn
    || isVecIndexSpecName fn || isVecIndexExecName fn
    || isArrayIndexGetName fn || isArrayFillForCopyTypesName fn
    || isSliceLenSpecName fn || isSliceLenExecName fn || isSliceIndexGetName fn
    || isBoxNewName fn || isArrayAsSliceName fn || isSliceIntoVecName fn
    || isCloneExecName fn || isWrappingAddName fn

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
    requireSupport .unit
    let idx ← resolveFreeVar unitTypeName
    pure (fvarTy idx)
  | .Tuple t1 t2 => do
    requireSupport .tuple
    let idx ← resolveFreeVar tupleTypeName
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
  | .USize | .ISize => pure (bvTy usizeBitWidth)
  | .Char => pure intTy
  | .StrSlice => pure strTy
  | .Array t _len? => do
    let elemTy ← typToBooleType t
    -- Preserve `len?` in VLIR (`Typ.Array`) for future contracts, but the
    -- current Boole model lowers both fixed arrays and slices to plain
    -- `Sequence T`.
    pure (seqTy elemTy)
  | .TypParam name => do
    let idx ← resolveFreeVar (sanitizeIdent name)
    pure (fvarTy idx)
  | .SpecFn params ret => do
    let retTy ← typToBooleType ret
    params.foldrM (fun p acc => do
      let pTy ← typToBooleType p
      pure (arrowTy pTy acc)) retTy
  | .Decorated _ inner => typToBooleType inner
  | .Struct name params => do
    -- A trait associated-type projection (`<Self as Trait>::Assoc`) is parsed as
    -- a nominal `Struct` whose Boole type name (e.g. `Ops_Arith_mul_Output`) no
    -- declaration backs.  When the in-program trait impl pins it to a concrete
    -- type, lower to that type instead (`assocTypeResolution`, built in
    -- `declsToBooleProgram`).
    match (← get).assocTypeResolution.get? (datatypeNameOf name) with
    | some resolved => typToBooleType resolved
    | none =>
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
    else if datatypeNameOf name == "Set" then
      requireSupport .set
      let idx ← resolveFreeVar "Set"
      let args ← params.toArray.mapM typToBooleType
      pure (fvarTy idx args)
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
    StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
  if params.isEmpty then
    ann none
  else
    let vars := params.toArray.map fun p =>
      BooleDDM.TypeVar.type_var default (ann p)
    ann (some (BooleDDM.TypeArgs.type_args default (ann vars)))

/-! ## Loop Control Helpers -/

/-- Allocate a fresh synthetic loop label of the form `vloop_N`, where `N`
    comes from `BuildCtx.loopLabelCounter`. Used when a `.Loop` has no
    source-level label but its body contains unlabeled `break`/`continue`
    that need a target — deriving the label from AST structure would
    risk collisions between structurally identical loops.  The `vloop_`
    prefix stays out of the `loop_N` / `loop_havoc_N` namespace that
    Strata's `LoopElim` transform uses for its synthesized blocks: the
    post-transform type check rejects label shadowing, so an emitted
    `loop_N` block enclosing a while loop would collide with the block
    `LoopElim` wraps that loop in. -/
private def implicitLoopLabel : BuildM String := do
  let n ← freshLoopLabelId
  pure (sanitizeIdent s!"vloop_{n}")

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
  | .Unary (.Clip _ _) _ => true
  | .Unary .Trigger e => exprHonorsExpectedInt e
  | .Unary (.HasType _) e => exprHonorsExpectedInt e
  | .Unary .Old e => exprHonorsExpectedInt e
  -- Datatype / tuple field projection: the `.Proj` / `.Proj'` arm coerces its
  -- result to `expected?` (the two paths mirror each other), so a nat-typed
  -- field used in an int comparison already lowers to `int`.  Without this the
  -- post-coerce safety net fires and double-wraps (`nat.toInt(nat.toInt(..))`).
  | .Unary (.Proj ..) _ => true
  | .Unary (.Proj' ..) _ => true
  | .If _ t f => exprHonorsExpectedInt t && exprHonorsExpectedInt f
  | .Bind _ body => exprHonorsExpectedInt body
  | .MatchBlock _ body => exprHonorsExpectedInt body
  | .Call _ _ _ => true
  | _ => false

private def arrayFillExpr (elem : BExpr) : BuildM BExpr := do
  requireSupport .arrayFill
  let fillIdx ← resolveFreeVar "Array_array_fill_for_copy_types"
  pure (Bld.app (Bld.fvar fillIdx) elem)

/-- Emit an empty-sequence literal for `elemTy`.  Concrete bv/int element
    types use Boole's dedicated typed constants (`Sequence.empty_<T>`, via
    `seqEmptyTokenName?`); every other element type — type parameters,
    structs, … — uses the polymorphic `Sequence.empty<T>()` form, which
    carries the element type explicitly through the Core `seq_empty`
    production. -/
private def seqEmptyExpr (elemTy : Typ) : BuildM BExpr := do
  match seqEmptyTokenName? elemTy with
  | some tok => pure (Bld.fvar (← resolveFreeVar tok))
  | none => pure (Bld.seqEmpty (← typToBooleType elemTy))

private def seqBuildExpr (seq elem : BExpr) : BuildM BExpr := do
  pure (Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.build")) [seq, elem])

/-- Map the underlying element type to its dedicated typed-literal AST
    constructor.  The Boole grammar declares `Sequence.of_<T>[v0, v1, …]`
    as `fn seq_of_<T> (vs : CommaSepBy Expr) : Sequence <T>`, so emission
    must produce the specific `BooleDDM.Expr.seq_of_<T>` AST node (which
    pretty-prints with brackets) — emitting a generic `appN` to
    `Sequence.of_bv32` would print as `Sequence.of_bv32(…)`, which the
    DDM frontend does not recognize.  Returns `none` for element types
    that have no typed token (polymorphic, structs, etc.). -/
private partial def seqLiteralCtor? : Typ → Option (Array BExpr → BExpr)
  | .Decorated _ inner    => seqLiteralCtor? inner
  | .UInt 8  | .SInt 8    => some (fun vs => .seq_of_bv8  default (ann vs))
  | .UInt 16 | .SInt 16   => some (fun vs => .seq_of_bv16 default (ann vs))
  | .UInt 32 | .SInt 32   => some (fun vs => .seq_of_bv32 default (ann vs))
  | .UInt 64 | .SInt 64   => some (fun vs => .seq_of_bv64 default (ann vs))
  | .USize | .ISize       => some (fun vs => .seq_of_bv64 default (ann vs))
  | .Int | .Nat           => some (fun vs => .seq_of_int  default (ann vs))
  | _ => none

/-- Emit a sequence literal.  When the element type has a typed
    `Sequence.of_<T>[…]` AST node (per `seqLiteralCtor?`), emit the
    compact literal form — Strata folds it back to the same build-chain
    internally, so verification semantics are unchanged, but the surface
    output is far more readable (especially for long constant tables like
    SHA-256's K32).  For non-bv/int element types (polymorphic, struct,
    decorated, …) fall back to the explicit `Sequence.build` chain. -/
private def seqLiteralExpr (elemTy : Typ) (elems : List BExpr) : BuildM BExpr := do
  match seqLiteralCtor? elemTy with
  | some ctor => pure (ctor elems.toArray)
  | none =>
    elems.foldlM (fun acc elem => seqBuildExpr acc elem) (← seqEmptyExpr elemTy)

/-- Emit `[elem; len]` as a sequence literal of `len` copies.  Threads the
    repeated element through `seqLiteralExpr` so bv/int element types pick
    up the compact `Sequence.of_<T>[elem, elem, …]` form; polymorphic
    element types still fall back to the explicit `Sequence.build` chain. -/
private def seqRepeatExpr (elemTy : Typ) (len : Nat) (elem : BExpr) : BuildM BExpr :=
  seqLiteralExpr elemTy (List.replicate len elem)

private def arrayFillOrRepeatExpr (expected? : Option Typ) (elem : BExpr) : BuildM BExpr := do
  match expected?.bind arrayLen? with
  | some len =>
    -- Element type comes from the `expected?` array's element type when
    -- known.  If the array shape is unrecognized we fall back to the
    -- untyped name, which will surface as a parser error — preferable to a
    -- silently-wrong typed pick.
    let elemTy := (expected?.bind arrayElemTyp?).getD .Empty
    seqRepeatExpr elemTy len elem
  | none => arrayFillExpr elem

private def indexedElemTyp? (env : VarEnv) (bound : BoundEnv) (container : Exp) :
    Option Typ :=
  (inferComparableTyp? env bound (unwrapViewCall container)).bind fun ty =>
    seqElemTyp? ty <|> vecElemTyp? ty <|> arrayElemTyp? ty

private def coerceIndexedResult (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) (container : Exp) (selected : BExpr) : BuildM BExpr := do
  let srcKind? := (indexedElemTyp? env bound container).bind numKindOfTyp?
  let tgtKind? := expected?.bind numKindOfTyp?
  coerceNumeric srcKind? tgtKind? selected

/-- Return the result type of a `SpecFn` (closure) type, peeling decorations. -/
private partial def specFnRetTy? : Typ → Option Typ
  | .Decorated _ t => specFnRetTy? t
  | .SpecFn _ r => some r
  | _ => none

/-- True for primitive scalar types (numbers, `bool`, `char`).  `Seq::map`
    synthesis is restricted to these: a closure over a primitive element
    can only have a primitive-arithmetic body, which translates cleanly to
    a first-order function.  Closures over tuples/structs/enums project
    datatype fields, and the resulting accessor applications hit a Strata
    typing gap once promoted out of an (un-type-checked) lambda — see the
    `crypto_noref` tuple closure.  Such closures fall back to the lambda
    form instead. -/
private partial def isPrimitiveScalarTyp : Typ → Bool
  | .Decorated _ t => isPrimitiveScalarTyp t
  | .Bool | .Int | .Nat | .Char => true
  | .UInt _ | .SInt _ | .USize | .ISize => true
  | _ => false

/-- Recover a `Seq::map` closure's result type from the `Box` wrapper that
    Verus emits around the closure argument.  VLIR drops the `.Call` type
    arguments, so this `Box`-carried `SpecFn` type is the reliable source. -/
private def boxedClosureRetTy? : Exp → Option Typ
  | .Unary (.Box bt) _ => specFnRetTy? bt
  | _ => none

/-- Synthesize a lambda-free replacement for a `Seq::map` / `Seq::map_values`
    call.  Strata's SMT encoder rejects closures handed to the uninterpreted
    `Seq_lib_map`, so instead of `Seq_lib_map(s, fun … => …)` we emit ordinary
    top-level declarations and call those:

      * `Seq_map_empty_<id>` — an uninterpreted empty result sequence, with an
        axiom pinning its length to 0.  Needed because Boole has no typed
        empty-sequence literal for element types like `nat`.
      * `Seq_map_closure_<id>` — a first-order `function` whose parameters are
        the closure's binders and whose body is the (already-translated)
        closure body.  No lambda, so it encodes to SMT cleanly.
      * `Seq_map_rec_<id>` — an `int`-recursive function that rebuilds the
        mapped sequence one element at a time, applying the closure function.

    The call site becomes `Seq_map_rec_<id>(seq, |seq|)`.  `seqB` is the
    translated source sequence; `closureBodyB` the translated closure body
    (lowered in a scope binding `closureParams`); `elemTy` the source element
    type; `retTy` the closure's result type. -/
private def emitSeqMapDecls
    (seqB closureBodyB : BExpr)
    (closureParams : List (String × Typ)) (elemTy retTy : Typ) :
    BuildM BExpr := do
  let id ← freshSynthId
  let emptyName := s!"Seq_map_empty_{id}"
  let closureName := s!"Seq_map_closure_{id}"
  let recName := s!"Seq_map_rec_{id}"
  addFreeVars #[emptyName, closureName, recName]
  let elemBTy ← typToBooleType elemTy
  let retBTy ← typToBooleType retTy
  let noTypeArgs : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
    ann none
  let noSpec : StrataDDM.Ann (Array (BooleDDM.SpecElt SourceRange)) SourceRange :=
    ann #[]
  -- (1) uninterpreted empty result sequence + length axiom.  Boole has no
  -- typed empty-sequence literal for element types like `nat`, so the empty
  -- base case of the recursion is an uninterpreted constant constrained to
  -- length 0.
  let emptyIdx ← resolveFreeVar emptyName
  let emptyCmd : BCmd :=
    .command_constdecl default (ann emptyName) noTypeArgs (Bld.seqTy retBTy)
  let emptyAxiom : BCmd :=
    .command_axiom default (ann none)
      (Bld.eq (Bld.seqLength (Bld.fvar emptyIdx)) (Bld.intConst 0))
  -- (2) first-order closure function: its parameters are the closure's
  -- binders and its body is the translated closure body.
  let closureBindingsArr ← closureParams.toArray.mapM (fun (name, ty) => do
    let bty ← typToBooleType ty
    pure (BooleDDM.Binding.mkBinding default (ann (sanitizeVarName name))
      (BooleDDM.TypeP.expr bty)))
  let closureBindings := BooleDDM.Bindings.mkBindings default (ann closureBindingsArr)
  let closureCmd : BCmd :=
    .command_fndef default (ann closureName) noTypeArgs closureBindings retBTy
      noSpec closureBodyB (ann none)
  -- (3) int-recursive map function: `map(s, n)` rebuilds the image of the
  -- length-`n` prefix of `s`, recursing `n → n - 1` with `decreases n`.
  let seqParamName := "s"
  let idxParamName := "n"
  let mapBindings := BooleDDM.Bindings.mkBindings default (ann #[
    BooleDDM.Binding.mkBinding default (ann seqParamName)
      (BooleDDM.TypeP.expr (Bld.seqTy elemBTy)),
    BooleDDM.Binding.mkBinding default (ann idxParamName)
      (BooleDDM.TypeP.expr Bld.intTy)])
  let mapOutTy := Bld.seqTy retBTy
  let closureIdx ← resolveFreeVar closureName
  let recIdx ← resolveFreeVar recName
  let (decrAnn, mapBody, recReqs) ← withScope do
    addBoundVars #[seqParamName, idxParamName]
    let sIdx ← match ← lookupBoundVar seqParamName with
      | some i => pure i
      | none => throw "emitSeqMapDecls: sequence parameter unbound"
    let nIdx ← match ← lookupBoundVar idxParamName with
      | some i => pure i
      | none => throw "emitSeqMapDecls: index parameter unbound"
    let sE := Bld.bvar sIdx
    let nE := Bld.bvar nIdx
    let nPrev := Bld.intSub nE (Bld.intConst 1)
    let cond := Bld.intLe nE (Bld.intConst 0)
    let selE := Bld.seqSelect sE nPrev
    -- `Seq::map` passes (index, element); `Seq::map_values` passes (element).
    let closureArgs := if closureParams.length ≥ 2 then [nPrev, selE] else [selE]
    let closureCall := Bld.appN (Bld.fvar closureIdx) closureArgs
    let recCall := Bld.appN (Bld.fvar recIdx) [sE, nPrev]
    let consE ← seqBuildExpr recCall closureCall
    let body := Bld.iteTyped mapOutTy cond (Bld.fvar emptyIdx) consE
    -- The recursion selects `s[n-1]` in its step case; carry the prefix-range
    -- precondition (gated by `SynthConfig.seqMapPrecond`) so that select's
    -- out-of-bounds obligation discharges.
    let cfg ← getSynthConfig
    let recReqs : Array (BooleDDM.SpecElt SourceRange) :=
      if cfg.seqMapPrecond then #[Synth.prefixRangeRequires sE nE] else #[]
    pure (Bld.mkMeasure (some nE), body, recReqs)
  let recDecl := BooleDDM.RecFnDecl.recfn_decl default (ann recName) noTypeArgs
    mapBindings mapOutTy (ann recReqs) decrAnn mapBody
  pushSynthDecl emptyCmd
  pushSynthDecl emptyAxiom
  pushSynthDecl closureCmd
  pushSynthDecl (.command_recfndefs default (ann #[recDecl]))
  pure (Bld.appN (Bld.fvar recIdx) [seqB, Bld.seqLength seqB])

/-! ### nat-native binop lowering

When a binary operation is in nat-space, we lower it to the prelude's
`nat.lt` / `nat.add` / … directly rather than the int round-trip
`nat.toInt(a) <op> nat.toInt(b)` (comparisons) or
`nat.fromInt(nat.toInt(a) <op> nat.toInt(b))` (arithmetic).  The result is
semantically identical — the prelude bodies expand to the int form — but the
translated spec stays in nat-space, matching the source and the hand-written
Strata reference.  `numBinopEmit` (below) dispatches to these; the two tables
here map an operator to its prelude function.

The two tables fire under deliberately *different* guards, kept side-by-side
here so the asymmetry is visible rather than buried in the `.Binary` arm:

  * `natCmpFn` fires on the *operand* types (`inferComparisonNumKind` reports
    both sides nat).  A comparison's result is always `bool`, so there is no
    "expected nat" hint to key on — the operands are the only signal.
  * `natArithFn?` fires on the *expected/result* type (`expectedKind == nat`),
    which `.Unary (.Clip .Nat _)` propagates down.  The operand types alone
    don't say whether the sum is wanted in nat-space (a nat `a + b` consumed
    in an int context is correctly lowered as int).

Final emission now flows through `NumDomain` / `numBinopEmit` below.  Domain
selection stays at the call sites because it is coupled to operand preparation:
scalar operands translate at the target mathematical type, while bv operands
must preserve the width-inference / narrow-then-widen / signedness-promotion
policy before emission. -/

/-- Prelude function for a nat-space comparison (always applicable when both
    operands are nat — see the table doc above). -/
def natCmpFn : InequalityOp → String
  | .Le => "nat.le"
  | .Lt => "nat.lt"
  | .Ge => "nat.ge"
  | .Gt => "nat.gt"

/-- Prelude function for a nat-space arithmetic op, or `none` if the op has no
    nat-native form.  `nat.sub` / `nat.div` / `nat.mod` are total, mirroring
    Verus's `nClip` / spec-level `/` / `%` — a `nat` underflow or a zero divisor
    yields an unspecified value, not a proof obligation (see `Nat.boole.st`). -/
def natArithFn? : BinaryOp → Option String
  | .Arith .Add _          => some "nat.add"
  | .Arith .Sub _          => some "nat.sub"
  | .Arith .Mul _          => some "nat.mul"
  | .Arith .EuclideanDiv _ => some "nat.div"
  | .Arith .EuclideanMod _ => some "nat.mod"
  | _                      => none

/-- The lowering domain of a numeric binary operation: a mathematical `nat`
    or `int`, or a width-`w` (un)signed bitvector. -/
inductive NumDomain where
  | nat
  | int
  | bv (w : Nat) (signed : Bool)
  deriving Repr, DecidableEq

/-- Unified emitter table: build `op` applied to already-prepared operands
    `l`, `r` in lowering `domain`.  This is the single
    `(domain, op) → Boole expression` dispatch the comparison and arithmetic
    arms share.  Operand *preparation* stays in those arms (it differs per
    domain — translating leaves at the domain scalar type for nat/int, or the
    bv width-inference dance for bv), but emission funnels through here.

    Returns `none` when `op` has no lowering in `domain`: bitwise ops on
    nat/int (see `natArithFn?`).

    Domain conventions:
      * `nat` → the prelude functions (`natCmpFn` / `natArithFn?`).
      * `int` → `applyBinaryOp`, which already maps every arith/inequality
        op to its `int` builder.
      * `bv w signed` → `applyBv*` builders; `signed` picks the U/S variant
        for compares and div/mod/shr.  Shift ops carry their own width
        (`Shl w` / `Shr w`); other bv ops use the domain width `w`. -/
def numBinopEmit (domain : NumDomain) (op : BinaryOp) (l r : BExpr) :
    BuildM (Option BExpr) := do
  match domain with
  | .int => pure (applyBinaryOp op l r)
  | .nat =>
    let fnName? : Option String := match op with
      | .Inequality cmp => some (natCmpFn cmp)
      | _ => natArithFn? op
    match fnName? with
    | some name => let idx ← resolveFreeVar name; pure (some (Bld.appN (Bld.fvar idx) [l, r]))
    | none => pure none
  | .bv w s =>
    match op with
    | .Inequality cmp =>
      let opName := match cmp with
        | .Le => if s then "SLe" else "ULe"
        | .Lt => if s then "SLt" else "ULt"
        | .Ge => if s then "SGe" else "UGe"
        | .Gt => if s then "SGt" else "UGt"
      pure (applyBvCmpOp w opName l r)
    | .Arith a _ =>
      let opName := match a with
        | .Add => "Add"
        | .Sub => "Sub"
        | .Mul => "Mul"
        -- `SDiv`/`SMod` are SMT `bvsdiv`/`bvsrem`: truncate toward zero, with the
        -- remainder taking the sign of the dividend.  That is Rust's run-time
        -- `/`/`%` — exactly `TruncDiv`/`TruncRem`.  The Euclidean ops reuse the
        -- same lowering as an approximation, exact for a non-negative dividend
        -- (Strata has no `bvsmod`); should Strata gain genuine Euclidean ops,
        -- only the Euclidean rows move, leaving the truncated exec ops correct.
        | .EuclideanDiv | .TruncDiv => if s then "SDiv" else "UDiv"
        | .EuclideanMod | .TruncRem => if s then "SMod" else "UMod"
      pure (applyBvBinOp w opName l r)
    | .Bitwise bitop _ =>
      -- Shift ops carry their own width; and/or/xor use the domain width.
      let opW := match bitop with
        | .Shl sw _ | .Shr sw => sw
        | _ => w
      let opName := match bitop with
        | .BitAnd => "And"
        | .BitOr => "Or"
        | .BitXor => "Xor"
        | .Shl _ _ => "Shl"
        | .Shr _ => if s then "SShr" else "UShr"
      if opName == "SShr" then
        -- Signed shift right: no direct builder, resolve the fvar.
        let fnIdx ← resolveFreeVar s!"Bv{opW}.SShr"
        pure (some (Bld.appN (Bld.fvar fnIdx) [l, r]))
      else
        pure (applyBvBitOp opW opName l r)
    | _ => pure (applyBinaryOp op l r)


/-- Rule ③'s narrowing gate: a cast to a fixed-width integer type whose
    translation runs in the int domain keeps its wrap-around semantics unless
    the inner's source type syntactically fits the target — `(x : u128) as u64`
    is `x mod 2^64`, not `x`.  Unsigned targets wrap with `mod 2^w`; signed
    targets wrap to the centered range via `(x + 2^(w-1)) mod 2^w - 2^(w-1)`
    (Euclidean mod, so this is two's-complement reinterpretation).  Inners
    whose source type cannot be read syntactically — arithmetic trees, calls
    returning `nat`/`int` — wrap conservatively: eliding on a provable-but-
    unread bound would silently change the statement (e.g. vstd's
    `lemma_u128_shr_is_div` companion `(x as u64) % …` facts). -/
private def clipWrapIntModeled (env : VarEnv) (bound : BoundEnv)
    (target : Nat × Bool) (e : Exp) (inner : BExpr) : BExpr :=
  let srcTy? := inferComparableTyp? env bound e <|>
    (match e with | .Const _ t => some t | _ => none)
  let fits := match srcTy?.bind fixedWidthInfoOfTyp with
    | some src => fitsFixedWidth src target
    | none => false
  if fits then inner
  else
    let (tw, tsigned) := target
    let full := Bld.intConst ((2 : Int) ^ tw)
    if tsigned then
      let half := Bld.intConst ((2 : Int) ^ (tw - 1))
      Bld.intSub (Bld.intMod (Bld.intAdd inner half) full) half
    else
      Bld.intMod inner full


/-- Positional projection from a tuple value.  Tuple types lower to
    right-nested binary pairs — `(A, B, C)` is `Tuple2 A (Tuple2 B C)`,
    mirroring the parser's right fold — so field `k` of a `size`-tuple is
    `Tuple2.._0` after `k` hops of `Tuple2.._1`, except the last field, which
    is the bare `Tuple2.._1` spine.  A 1-tuple carries no wrapper (its type
    lowers to the payload type), so projection is the identity. -/
private def tupleProjChain (size field : Nat) (x : BExpr) : BuildM BExpr := do
  if field ≥ size then
    throw s!"tuple projection out of range: field {field} of a {size}-tuple"
  if size == 1 then
    return x
  requireSupport .tuple
  let sndIdx ← resolveFreeVar tupleSndSelector
  let spine := (List.range (min field (size - 1))).foldl
    (fun acc _ => Bld.app (Bld.fvar sndIdx) acc) x
  if field == size - 1 then
    return spine
  else
    let fstIdx ← resolveFreeVar tupleFstSelector
    return Bld.app (Bld.fvar fstIdx) spine

private partial def typContainsTypeParam : Typ → Bool
  | .TypParam _ => true
  | .Tuple a b => typContainsTypeParam a || typContainsTypeParam b
  | .Array t _ => typContainsTypeParam t
  | .SpecFn params ret => params.any typContainsTypeParam || typContainsTypeParam ret
  | .Decorated _ t => typContainsTypeParam t
  | .Struct _ params | .Enum _ params => params.any typContainsTypeParam
  | _ => false

/-- Strata's Boole surface does not always propagate datatype selector type
    arguments through polymorphic tuple selectors in bitvector contexts:
    `Tuple2.._0(kv) ^ Tuple2.._1(kv)` may leave the operands at unrelated
    selector type variables even when `kv : Tuple2 bv8 bv8`.  For closed,
    bitvector-valued projections, synthesize a tiny monomorphic helper with an
    explicit return type and call that helper instead. -/
private def synthTupleProjHelper (size field : Nat) (containerTy fieldTy : Typ) :
    BuildM BExpr := do
  -- Reuse one helper per `(arity, field, container type)`; the field type is
  -- determined by the container, so this key is sufficient.
  let key := (size, field, containerTy)
  let name ← match (← get).tupleProjHelpers[key]? with
    | some name => pure name
    | none => do
      let id ← freshSynthId
      let name := s!"Tuple2_proj_{size}_{field}_{id}"
      addFreeVars #[name]
      let argName := "tuple_arg"
      let inputTy ← typToBooleType containerTy
      let outputTy ← typToBooleType fieldTy
      let inputBinding :=
        BooleDDM.Binding.mkBinding default (ann argName)
          (BooleDDM.TypeP.expr inputTy)
      let inputBindings := BooleDDM.Bindings.mkBindings default (ann #[inputBinding])
      let noTypeArgs : StrataDDM.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
        ann none
      let noSpec : StrataDDM.Ann (Array (BooleDDM.SpecElt SourceRange)) SourceRange :=
        ann #[]
      let body ← withScope do
        addBoundVars #[argName]
        tupleProjChain size field (Bld.bvar 0)
      pushSynthDecl (.command_fndef default (ann name) noTypeArgs inputBindings outputTy
        noSpec body (ann none))
      modify (fun ctx =>
        { ctx with tupleProjHelpers := ctx.tupleProjHelpers.insert key name })
      pure name
  let idx ← resolveFreeVar name
  pure (Bld.fvar idx)

private def tupleProjMayNeedHelper (containerTy fieldTy : Typ) : Bool :=
  !typContainsTypeParam containerTy && (bitInfoOfTyp fieldTy).isSome

/-- Tuple value from positional element expressions, as right-nested
    constructor applications — `(a, b, c)` is
    `Tuple2_ctor_2(a, Tuple2_ctor_2(b, c))` — mirroring the type lowering.
    A single element is the payload itself (1-tuples carry no wrapper). -/
private def tupleCtorChain : List BExpr → BuildM BExpr
  | [] => throw "cannot build an empty tuple value"
  | [a] => return a
  | a :: rest => do
    requireSupport .tuple
    let ctorIdx ← resolveFreeVar tupleCtorName
    let tail ← tupleCtorChain rest
    return Bld.appN (Bld.fvar ctorIdx) [a, tail]

/-- Peel `Box`/`Unbox` coercion wrappers (typing artifacts with no Boole
    counterpart) off an expression's spine. -/
private partial def stripBoxWrappers : Exp → Exp
  | .Unary (.Box _) e | .Unary (.Unbox _) e => stripBoxWrappers e
  | e => e

/-- A multi-binder `choose|v1, …, vn| pred` whose chosen value is the binder
    tuple `(v1, …, vn)` normalizes to a single-binder choose over the product
    type — `choose p : (T1, …, Tn) :: pred[vk := p.k]` with chosen value `p` —
    which is the shape Boole's one-binder `choose_assign` statement and the
    spec-fn choice axiom can express.  Verus lowers
    `let (x, y) = choose|i, j| pred(i, j)` through exactly this tuple shape
    (the destructure is separate `Proj'` assignments).  The product binder
    name is derived from the source binders, uniquified against the
    predicate's free variables.  Single-binder chooses and any other body
    shape pass through unchanged. -/
private def normalizeChooseProduct : Exp → Exp
  | e@(.Bind (.Choose vars pred) chooseBody) => Id.run do
    if vars.length < 2 then return e
    let .TupleCtor n elems := stripBoxWrappers chooseBody | return e
    if n != vars.length || elems.length != vars.length then return e
    let elemVars := elems.map stripBoxWrappers
    let isBinderTuple := (elemVars.zip vars).all fun (el, (v, _)) =>
      match el with | .Var x => x == v | _ => false
    if !isBinderTuple then return e
    let free := expVarRefs pred
    let baseName := String.intercalate "_" (vars.map Prod.fst) ++ "_choose"
    let mut pairName := baseName
    while free.contains pairName do
      pairName := pairName ++ "_"
    let prodTy := match (vars.map Prod.snd).reverse with
      | [] => Typ.Empty
      | last :: rest => rest.foldl (fun acc ty => .Tuple ty acc) last
    let subs := vars.zipIdx.map fun ((v, _), k) =>
      (v, Exp.Unary (.Proj' n k) (.Var pairName))
    let pred' := substExps subs pred
    return .Bind (.Choose [(pairName, prodTy)] pred') (.Var pairName)
  | e => e

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
     lhsNum? == some .nat || rhsNum? == some .nat ||
     lhsNum? == some .int || rhsNum? == some .int)
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
    -- Non-numeric (e.g. sequence) comparisons: neither side carries a bv
    -- `argTy?`, so without help the literal side gets `expected? = none`
    -- and any `Sequence.empty` inside it falls back to the untyped name.
    -- Use `inferComparableTyp?` to read the typed side's concrete type and
    -- propagate it as `expected?` to the OTHER side.
    let lExpected? := lExpected? <|> inferComparableTyp? env bound rhs
    let rExpected? := rExpected? <|> inferComparableTyp? env bound lhs
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let targetInfo? := argTy?.bind bitInfoOfTyp
    let l ← coerceBvBv lhsInfo? targetInfo? l0
    let r ← coerceBvBv rhsInfo? targetInfo? r0
    return (argTy?, l, r)

/-- Prepare both operands of a scalar (`nat` / `int`) binary op by translating
    each at the domain scalar type `ty`, so the leaves coerce to that domain.
    The bv domain prepares operands differently (width-inference dance) and so
    stays inline in the `.Binary` arm.  Emission of the prepared operands is
    shared via `numBinopEmit`. -/
partial def prepScalarOperands (env : VarEnv) (bound : BoundEnv)
    (ty : Typ) (lhs rhs : Exp) : BuildM (BExpr × BExpr) := do
  let l ← expToBoole env bound (some ty) lhs
  let r ← expToBoole env bound (some ty) rhs
  pure (l, r)


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
    -- could not propagate. Do not fall back to source `.Nat` here: Verus
    -- often serializes plain integer literals as nat even inside int
    -- arithmetic, so nat lifting must be driven by the surrounding expected
    -- type.
    let effectiveTy? :=
      expected? <|>
        (if (bitWidthOfTyp ty).isSome then some ty else none)
    let raw := constToBoole effectiveTy? c
    let rawKind? :=
      match c with
      | .Int _ | .Char _ =>
        match effectiveTy?.bind bitInfoOfTyp with
        | some (w, signed) => some (.bv w signed)
        | none => some .int
      | _ => none
    let targetKind? := effectiveTy?.bind numKindOfTyp?
    coerceNumeric rawKind? targetKind? raw
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
    if size == 0 then
      requireSupport .unit
      let ctorIdx ← resolveFreeVar unitCtorName
      return Bld.fvar ctorIdx
    -- Decompose a known tuple `expected?` into per-element types so a widened
    -- element (an erased `as int` over a bare projection/variable that carries
    -- no `Box{Int}`) is coerced to the slot type, instead of leaving a `bv`
    -- value in an `int`/`nat` tuple field.  Mirrors the `StructCtor` /
    -- `ArrayLiteral` element-type propagation; a non-tuple or generic
    -- `expected?` yields `none` per element (the conservative default).
    let args ← data.zipIdx.mapM (fun (e, i) =>
      expToBoole env bound (expected?.bind (tupleFieldTyp? size i)) e)
    tupleCtorChain args
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
    -- Select the lowering domain + prepare operands, then dispatch via the
    -- unified `numBinopEmit`.  nat fires on the operand types (a comparison's
    -- result is `bool`, so there is no expected-nat hint); otherwise
    -- `comparisonPrelude` chooses int vs bv and prepares the operands.
    let (domain, l, r) ← do
      if inferComparisonNumKind env bound lhs == some .nat &&
         inferComparisonNumKind env bound rhs == some .nat then
        let (l, r) ← prepScalarOperands env bound Typ.Nat lhs rhs
        pure (NumDomain.nat, l, r)
      else
        let (argTy?, l, r) ← comparisonPrelude env bound lhs rhs
        let domain ← match argTy? with
          | some ty =>
            match bitInfoOfTyp ty with
            | some (w, s) => pure (NumDomain.bv w s)
            | none => throw s!"internal error: expected bitvector comparison type, got {repr ty}"
          | none => pure NumDomain.int
        pure (domain, l, r)
    match ← numBinopEmit domain (.Inequality cmp) l r with
    | some result => return result
    | none => throw s!"unsupported comparison: {repr cmp} in domain {repr domain}"
  | .Binary .Index lhs rhs => do
    let seqExpr ← expToBoole env bound none lhs
    let intIdx ← expToBoole env bound (some .Int) rhs
    coerceIndexedResult env bound expected? lhs (Bld.seqSelect seqExpr intIdx)
  | .Binary op lhs rhs => do
    -- Run arith in `int` when the context demands int or any subtree
    -- mixes int and bv operands. Otherwise bv overflow corrupts the
    -- post-hoc `bv*_to_int_u` wrap (`n == 2^64 - 1` ↦ `bv64_to_int_u(n
    -- + 1bv64) == 0`).
    let expectedKind? := expected?.bind numKindOfTyp?
    -- nat-native lowering: nat-result arithmetic → `nat.add`/`nat.sub`/… (see
    -- the `natArithFn?` table doc).  Fires on the *expected* type, which
    -- `.Unary (.Clip .Nat _)` propagates down.  Operands are translated at
    -- `Nat`.  `nat.sub`/`nat.div`/`nat.mod` are total in the prelude, mirroring
    -- Verus's `nClip` / spec-level `/`/`%` (all total — a `nat` underflow or a
    -- division by zero is unspecified, not a proof obligation), so neither a
    -- `b <= a` nor a divisor-nonzero obligation is emitted.  `EuclideanMod`
    -- additionally fires on nat operand types: unlike
    -- `*`/`+`, a `nat % p` carries no nat-clip, so under an equality
    -- (`a % p == b % p`) there is no expected-nat hint to catch it.  Restricted
    -- to mod so `nat.sub`/`nat.div` keep their expected-driven firing.
    let natModByOperands :=
      (op matches .Arith .EuclideanMod _) &&
      inferComparisonNumKind env bound lhs == some .nat &&
      inferComparisonNumKind env bound rhs == some .nat
    match (if expectedKind? == some .nat || natModByOperands then natArithFn? op else none) with
    | some _ =>
      let (l, r) ← prepScalarOperands env bound Typ.Nat lhs rhs
      match ← numBinopEmit .nat op l r with
      -- Coerce the nat-domain result to the caller's expected kind: a `nat`
      -- result feeding an int/bv context (e.g. `(n % 2) as u8`, or `n % 2 == 0`
      -- under the int-fallback) must be `nat.toInt`-wrapped, not left as `nat`.
      | some result => return ← coerceNumeric (some .nat) expectedKind? result
      | none => throw s!"nat lowering missing for {repr op}"
    | none => pure ()
    let arithRunsInInt :=
      match op with
      | .Arith _ _ =>
        match expectedKind? with
        | some .int | some .nat => true
        | _ => expHasMixedIntBvArith env bound (.Binary op lhs rhs)
      | _ => false
    if arithRunsInInt then
      let (l, r) ← prepScalarOperands env bound Typ.Int lhs rhs
      match ← numBinopEmit .int op l r with
      | some result => return ← coerceNumeric (some .int) expectedKind? result
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
    -- A shift's operating width is its VALUE (lhs) operand's width, and the
    -- amount (rhs) must match it (SMT `bvshl`/`bvlshr` require equal-width
    -- operands).  A two-constant shift like `1u64 << 51` leaves
    -- `lhsInfo?`/`rhsInfo?` = none (no `.Const` case in `inferBitInfo`) ⇒
    -- `info? = none`, so each side would emit at its own VLIR width
    -- (`bv64 << bv32`), which Strata rejects.  Pin the width from the lhs type
    -- so `argTy?` forces both operands — value and amount — to it.
    let info? :=
      match op with
      | .Bitwise (.Shl _ _) _ | .Bitwise (.Shr _) _ =>
        let lhsTy? := inferComparableTyp? env bound lhs <|>
          (match lhs with | .Const _ t => some t | _ => none)
        info? <|> lhsTy?.bind bitInfoOfTyp
      | _ => info?
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    -- An arith op with no inferred bv width lowers in the int domain (see
    -- `domain` below), so its operands must arrive int-typed: translate them
    -- at `Int` so nat-kinded leaves — e.g. a nat-returning spec-fn call under
    -- an all-int-modeled tree like `x div pow2(e)` with `x : u128` — coerce
    -- via `nat.toInt` instead of feeding a bare `nat` to an int operator.
    -- (Trees with a bv operand never reach this: either `arithRunsInInt`
    -- routed them through the int path already, or `info?` is set.)
    let argTy? := match argTy?, op with
      | none, .Arith _ _ => some Typ.Int
      | t, _ => t
    -- Preserve narrow-then-widen for Verus's bit-vector proof mode: only
    -- push `argTy?` when the operand has no natural bv width of its own
    -- (e.g. a literal). See `bitvector_basic::test10` for the failure mode.
    let lExpected? := if lhsInfo?.isSome then none else argTy?
    let rExpected? := if rhsInfo?.isSome then none else argTy?
    let l0 ← expToBoole env bound lExpected? lhs
    let r0 ← expToBoole env bound rExpected? rhs
    let l ← coerceBvBv lhsInfo? info? l0
    let r ← coerceBvBv rhsInfo? info? r0
    -- Domain: bv when a width was inferred; otherwise int for arith / bool
    -- ops.  Bitwise with no inferred width defaults to bv `usize`, preserving
    -- the prior `resolvedW := w?.getD usizeBitWidth` behaviour.
    let domain := match info? with
      | some (w, s) => NumDomain.bv w s
      | none => match op with
        | .Bitwise _ _ => NumDomain.bv usizeBitWidth false
        | _ => NumDomain.int
    match ← numBinopEmit domain op l r with
    | some result =>
      -- Honor an int/nat result context even when the op lowered to bv.  A
      -- bitwise/shift op has no int form, so it emits bv; when the surrounding
      -- expression is int-modeled it must be cast up (e.g. `(1u64 << 54)` inside
      -- `77 * ((1u64<<54)*(1u64<<54)) <= u128::MAX` — B1 `mul_boundary_spec`).
      -- Only fires for an int/nat expected kind, so pure-bv/none contexts are
      -- byte-for-byte unchanged.
      match expectedKind? with
      | some .int | some .nat =>
        let domainKind : Option NumKind := match domain with
          | .int => some .int
          | .nat => some .nat
          | .bv w s => some (.bv w s)
        coerceNumeric domainKind expectedKind? result
      | _ => return result
    | none => throw s!"unsupported binary op: {repr op} in domain {repr domain}"
  | .Unary op e => do
    let x ←
      match op with
      | .Clip range _ =>
        -- Numeric cast (rule ③).  The target type's modeled *domain*
        -- (`numKindOfTyp?`) decides the handling, covering widening, narrowing,
        -- and `as int` uniformly:
        --   • int-modeled target (`u128`/`i128`, or `as int`): compute the inner
        --     in int — no wrap — then coerce to the outer expected.
        --   • `as nat`: inner at nat, or int/bv per the outer expected.
        --   • bv-width target (`u8`..`u64`/`usize`/`isize`): if the outer wants
        --     int the overflow clip is redundant (int doesn't overflow) → pass
        --     through int; else if the inner is int-modeled, recompute in int and
        --     cast int→bv; else bv→bv with narrow-then-widen.
        let targetTy : Typ := match range with
          | .U w => .UInt w.toNat
          | .I w => .SInt w.toNat
          | .USize => .USize
          | .ISize => .ISize
          | .Int => .Int
          | .Nat => .Nat
          -- `as char` / non-numeric target: `numKindOfTyp?` is `none`, so the
          -- `none` branch below passes the inner through (the old catch-all).
          | .Char => .Char
        match numKindOfTyp? targetTy with
        | some .int =>
          let inner ← expToBoole env bound (some Typ.Int) e
          -- Narrowing gate: `u128`/`i128` targets are fixed-width even though
          -- int-modeled, so they wrap unless the inner fits; a width-less
          -- `as int` passes through.
          let inner := match fixedWidthInfoOfTyp targetTy with
            | some tgt => clipWrapIntModeled env bound tgt e inner
            | none => inner
          coerceNumeric (some .int) (expected?.bind numKindOfTyp?) inner
        | some .nat =>
          match expected?.bind numKindOfTyp? with
          | some .int => expToBoole env bound (some Typ.Int) e
          | some (.bv w signed) => do
            let x ← expToBoole env bound (some Typ.Int) e
            coerceNumeric (some .int) (some (.bv w signed)) x
          | _ => expToBoole env bound (some Typ.Nat) e
        | some (.bv tw ts) =>
          if expected? == some Typ.Int then do
            -- Narrowing gate (int-context form): the int domain has no
            -- overflow, but the CAST still truncates when the inner's type
            -- does not fit the target width.
            let inner ← expToBoole env bound (some Typ.Int) e
            pure (clipWrapIntModeled env bound (tw, ts) e inner)
          else
            let innerInfo? := inferBitInfo env bound e
            match innerInfo? with
            | none =>
              -- inner has no bv width ⇒ int-modeled (e.g. a `u128` narrowed by
              -- `as u64`): recompute in int and cast int→bv (`coerceBvBv` can't).
              let xi ← expToBoole env bound (some Typ.Int) e
              coerceNumeric (some .int) (some (.bv tw ts)) xi
            | some _ =>
              let isWidening := match innerInfo? with
                | some (iw, _) => decide (iw < tw) | none => false
              let hint? := if isWidening then
                innerInfo?.map (fun (iw, s) => if s then Typ.SInt iw else Typ.UInt iw)
              else some targetTy
              let x0 ← expToBoole env bound hint? e
              coerceBvBv innerInfo? (some (tw, ts)) x0
        | none => expToBoole env bound expected? e
      | .Unbox t => do
        let inner ← expToBoole env bound (some t) e
        let srcKind? := numKindOfTyp? t
        let tgtKind? := expected?.bind numKindOfTyp?
        coerceNumeric srcKind? tgtKind? inner
      | .Box t => do
        -- When the surrounding context expects int, the Box's type
        -- assertion (typically `USize` for indices into `index_set`)
        -- is just a type-erasure artifact and would force a wasteful
        -- `bv64_to_int_u(int_to_bv64_u(...))` round-trip on an
        -- already-int operand (loop counters, post our `i : int`
        -- choice).  Skip the Box's coercion in that case.
        if expected? == some Typ.Int then
          expToBoole env bound (some Typ.Int) e
        else
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
      | .Length =>
        let seqExpr ← expToBoole env bound none e
        coerceNumeric (some .int) (expected?.bind numKindOfTyp?) (seqLength seqExpr)
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
    | .MutRefCurrent =>
      -- Value of a `&mut` place now: the operand itself, under the explicit
      -- mutable-state renames the translator maintains.
      return x
    | .MutRefFuture =>
      -- Post-state reads of mut params are rewritten to `<n>_out` before
      -- lowering (`substMutRefFutureOuts`); a future read that reaches here
      -- is loop-machinery ghost state whose value the renames already track.
      return x
    | .Box _ => return x
    | .Unbox _ => return x
    | .HasType _ => return x
    | .Length => return x
    | .Proj dt variant field _getVariant check => do
      if check == .Yes then
        throw s!"unsupported checked field projection: {dt}::{variant}.{field}"
      let projField := projFieldNameOf dt variant field
      let projIdx ← resolveFreeVar (datatypeDestructorNameOf dt projField)
      let projected := Bld.app (Bld.fvar projIdx) x
      -- The destructor yields the field at its source type; when the use site
      -- expects a wider numeric kind (an erased `as int`/widening cast pushed
      -- down here), insert a result-side coercion, mirroring the tuple
      -- projection path below.
      coerceNumeric ((enumFieldExpectedType? env dt variant field).bind numKindOfTyp?)
        (expected?.bind numKindOfTyp?) projected
    | .IsVariant dt variant => do
      let testerIdx ← resolveFreeVar (enumTesterNameOf dt variant)
      return Bld.app (Bld.fvar testerIdx) x
    | .Proj' size field =>
      -- The parser encodes a tuple's `IsVariant(x, tuple%N)` test as `Proj' N N`,
      -- reading the field index from the `tuple%N` variant string (which equals
      -- the arity).  A tuple has a single constructor, so the test is always true.
      if field == size then
        return boolConst true
      else do
        match (inferComparableTyp? env bound e).bind (tupleFieldTyp? size field),
            inferComparableTyp? env bound e with
        | some fieldTy, some containerTy =>
          if tupleProjMayNeedHelper containerTy fieldTy then do
            -- A synthesized helper forces a concrete bitvector type; align it
            -- with the use site's expected numeric kind.
            let helper ← synthTupleProjHelper size field containerTy fieldTy
            coerceNumeric (numKindOfTyp? fieldTy) (expected?.bind numKindOfTyp?)
              (Bld.app helper x)
          else do
            let projected ← tupleProjChain size field x
            -- Only int/nat fields are safe to coerce here.  A bv field that
            -- reaches this branch sits in a container carrying a type parameter
            -- (closed bv containers take the monomorphic-helper branch above),
            -- so its positional selector is typed at a type variable and a width
            -- cast on it would be ill-typed.  An int/nat field's selector type is
            -- concrete, so widening it to the expected kind is sound.
            match numKindOfTyp? fieldTy with
            | some .int | some .nat =>
              coerceNumeric (numKindOfTyp? fieldTy) (expected?.bind numKindOfTyp?) projected
            | _ => pure projected
        | _, _ =>
          tupleProjChain size field x
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
    -- For Seq_* whose result is a `Sequence T`, prefer the call's
    -- `expected?` (which may be concrete, e.g. `Sequence bv32` from a
    -- comparison context) over the polymorphic static signature
    -- (`Sequence (TypParam "T")`).  This lets nested
    -- `Sequence.append` / `Sequence.build` chains thread a concrete
    -- element type down to `Sequence.empty_<T>` literals at the
    -- leaves.  When `expected?` is not a `Sequence …`, fall back to
    -- the static signature.
    let seqArgExpected? : Option Typ :=
      if (expected?.map isSeqTyp).getD false then expected?
      else lookupFnParamTypeFull env fnameStr 0
    let mkFallback := do
      -- Some library fns have abstract declarations emitted as support decls
      -- (not in the prelude text) because they are polymorphic/higher-order
      -- and would fail SMT encoding if declared-but-unused (`Seq_lib_map`,
      -- `Set_finite`, …) or because their types reference other support
      -- decls (`Seq_lib_zip_with`'s `Tuple`).  A call here is the
      -- emitted-level signal that the decl is actually used, so register the
      -- need so the declaration appears in the final program.
      if let some need := Support.supportDeclForName? fnameStr then
        requireSupport need
        -- The Set-typed Seq builtins also need the `Set` type declared.
        match need with
        | .seqLibToSet | .setFinite => requireSupport .set
        | _ => pure ()
      let args' ← argsFiltered.zipIdx.mapM (fun (arg, idx) => do
        let paramTy? := lookupFnParamTypeFull env fnameStr idx
        let argExpected? := paramTy? <|> (match expected? with
          | some ty => if isIntTyp ty then some Typ.Int else none
          | none => none)
        expToBoole env bound argExpected? arg)
      let fnIdx ← resolveFreeVar fnameStr
      let app := Bld.appN (Bld.fvar fnIdx) args'
      let srcKind? := (lookupFnRetTypeFull env fnameStr).bind numKindOfTyp?
      let tgtKind? := expected?.bind numKindOfTyp?
      coerceNumeric srcKind? tgtKind? app
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
    else if isArrayIndexGetName fname then
      -- `Sequence.select` is indexed by `int`, so we ask the index
      -- translator for an int directly rather than translating with
      -- `expected = none` and post-coercing — that path doesn't fold
      -- a bv-typed `Const` literal into `intConst`, leaving an
      -- avoidable `bv64_to_int_u(bv{64}(0))` round-trip in output.
      match argsFiltered with
      | [arrayArg, indexArg] =>
        let arrayExpr ← expToBoole env bound none arrayArg
        let intIdx ← expToBoole env bound (some .Int) indexArg
        coerceIndexedResult env bound expected? arrayArg (Bld.seqSelect arrayExpr intIdx)
      | _ => mkFallback
    else if isArrayFillForCopyTypesName fname then
      match argsFiltered with
      | [elemArg] =>
        let elemExpected? := expected?.bind arrayElemTyp?
        let elemExpr ← expToBoole env bound elemExpected? elemArg
        arrayFillOrRepeatExpr expected? elemExpr
      | _ => mkFallback
    else if isWrappingAddName fname then
      -- `wrapping_add` is a procedure call only at the surface; bv-add
      -- is already mod-2^N in SMT bv semantics, so inline it as a flat
      -- `bvAdd width x y` to avoid forcing the solver across a procedure
      -- boundary with a conditional ensures.  Width comes from the
      -- expected return type if known, otherwise from the first arg's
      -- inferred numeric kind.
      match argsFiltered with
      | [xArg, yArg] =>
        let infoFromExpected := expected?.bind bitInfoOfTyp
        let infoFromArg :=
          match inferNumKind env bound xArg with
          | some (.bv w signed) => some (w, signed)
          | _ => none
        match infoFromExpected.orElse (fun _ => infoFromArg) with
        | some (w, signed) =>
          let argTy := bitTypOfInfo w signed
          let xExpr ← expToBoole env bound (some argTy) xArg
          let yExpr ← expToBoole env bound (some argTy) yArg
          let sum := Bld.bvAdd w xExpr yExpr
          coerceNumeric (some (.bv w signed)) (expected?.bind numKindOfTyp?) sum
        | none => mkFallback
      | _ => mkFallback
    else if isSliceLenSpecName fname || isSliceLenExecName fname then
      -- Slices are translated as `Sequence T`, so `slice.len()` lowers
      -- directly to `Sequence.length(slice)` (returning int) — no need for
      -- an uninterpreted `Slice_spec_slice_len` helper.  The exec-side
      -- `Slice_len` procedure stub becomes dead after this inlining and is
      -- dropped via `isVec2SeqDroppedDecl`; the spec-side
      -- `vstd::slice::spec_slice_len` is unreferenced after this and is
      -- dropped by `pruneUnreferencedVstdSpecs`.
      match argsFiltered with
      | [sliceArg] =>
        let sliceExpr ← expToBoole env bound none sliceArg
        let intLen := seqLength sliceExpr
        coerceNumeric (some .int) (expected?.bind numKindOfTyp?) intLen
      | _ => mkFallback
    else if isSliceIndexGetName fname then
      -- See `isArrayIndexGetName` arm: ask for int directly so a
      -- bv-typed literal index folds to `intConst` instead of going
      -- through a redundant `bv64_to_int_u(bv{64}(0))` cast.
      match argsFiltered with
      | [sliceArg, indexArg] =>
        let sliceExpr ← expToBoole env bound none sliceArg
        let intIdx ← expToBoole env bound (some .Int) indexArg
        coerceIndexedResult env bound expected? sliceArg (Bld.seqSelect sliceExpr intIdx)
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
      -- `Sequence.select` is indexed by `int`, so we ask the index
      -- translator for int directly — see the `isArrayIndexGetName`
      -- arm for the rationale (folding `bv{64}(K)` literals to
      -- `intConst K` instead of leaving a `bv64_to_int_u` cast).
      match argsFiltered with
      | [vArg, iArg] =>
        let seqExpr ← expToBoole env bound none (unwrapViewCall vArg)
        let intIdx ← expToBoole env bound (some .Int) iArg
        let selectIdx ← resolveFreeVar "Sequence.select"
        let selected := Bld.appN (Bld.fvar selectIdx) [seqExpr, intIdx]
        coerceIndexedResult env bound expected? vArg selected
      | _ => mkFallback
    else if fnameStr == "Seq_index" then
      match argsFiltered with
      | [sArg, iArg] =>
        let selected ← mkSeqBuiltinCall "select"
          [(sArg, lookupFnParamTypeFull env fnameStr 0), (iArg, some .Int)]
        coerceIndexedResult env bound expected? sArg selected
      | _ => mkFallback
    else if fnameStr == "Seq_first" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let zero := intConst 0
        let selectIdx ← resolveFreeVar "Sequence.select"
        let selected := Bld.appN (Bld.fvar selectIdx) [s, zero]
        coerceIndexedResult env bound expected? sArg selected
      | _ => mkFallback
    else if fnameStr == "Seq_last" then
      match argsFiltered with
      | [sArg] =>
        let s ← expToBoole env bound (lookupFnParamTypeFull env fnameStr 0) sArg
        let one := intConst 1
        let selected := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.select"))
          [s, intSub (seqLength s) one]
        coerceIndexedResult env bound expected? sArg selected
      | _ => mkFallback
    else if fnameStr == "Seq_empty" then do
      -- Pick the element type from the propagated `expected?` (a
      -- `Sequence T` or `Vec T` type when the surrounding context has
      -- one).  When neither is available we fall back to the untyped
      -- `Sequence.empty`, which surfaces as a parser error rather than a
      -- silently-wrong typed pick.
      let elemTy :=
        (expected?.bind seqElemTyp?).orElse (fun _ => expected?.bind vecElemTyp?)
          |>.getD .Empty
      seqEmptyExpr elemTy
    else if isVecNewExecName fname || isVecWithCapacityExecName fname then
      -- `Vec::new()` / `Vec::with_capacity(n)` both create an empty vector
      -- (the capacity hint does not change the length).  With `Vec :=
      -- Sequence`, the result is `Sequence.empty`; the element type comes
      -- from the surrounding context (the binding's Vec/Seq type).  Any
      -- capacity argument is discarded.
      let elemTy :=
        (expected?.bind vecElemTyp?).orElse (fun _ => expected?.bind seqElemTyp?)
          |>.getD .Empty
      seqEmptyExpr elemTy
    else if fnameStr == "Seq_update" then
      match argsFiltered with
      | [sArg, iArg, vArg] =>
        let elemTy? := seqArgExpected?.bind seqElemTyp?
            <|> lookupFnParamTypeFull env fnameStr 2
        mkSeqBuiltinCall "update"
          [(sArg, seqArgExpected?), (iArg, some .Int), (vArg, elemTy?)]
      | _ => mkFallback
    else if fnameStr == "Seq_push" then
      match argsFiltered with
      | [sArg, vArg] =>
        let elemTy? := seqArgExpected?.bind seqElemTyp?
            <|> lookupFnParamTypeFull env fnameStr 1
        mkSeqBuiltinCall "build" [(sArg, seqArgExpected?), (vArg, elemTy?)]
      | _ => mkFallback
    else if fnameStr == "Seq_take" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "take" [(sArg, seqArgExpected?), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_skip" then
      match argsFiltered with
      | [sArg, nArg] =>
        mkSeqBuiltinCall "skip" [(sArg, seqArgExpected?), (nArg, some .Int)]
      | _ => mkFallback
    else if fnameStr == "Seq_add" then
      match argsFiltered with
      | [s1Arg, s2Arg] =>
        mkSeqBuiltinCall "append"
          [(s1Arg, seqArgExpected?), (s2Arg, seqArgExpected?)]
      | _ => mkFallback
    else if fnameStr == "Seq_subrange" then
      match argsFiltered with
      | [sArg, startArg, endArg] =>
        let s ← expToBoole env bound seqArgExpected? sArg
        let start ← expToBoole env bound (some .Int) startArg
        let stop ← expToBoole env bound (some .Int) endArg
        let subrangeIdx ← resolveFreeVar "Sequence.subrange"
        return Bld.appN (Bld.fvar subrangeIdx) [s, start, stop]
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
        let s ← expToBoole env bound seqArgExpected? sArg
        let one := intConst 1
        let lenMinusOne := intSub (seqLength s) one
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, lenMinusOne]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_remove" then
      match argsFiltered with
      | [sArg, iArg] =>
        let s ← expToBoole env bound seqArgExpected? sArg
        let i ← expToBoole env bound (some .Int) iArg
        let one := intConst 1
        let suffixStart := intAdd i one
        let prefixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.take")) [s, i]
        let suffixSeq := Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.drop")) [s, suffixStart]
        return Bld.appN (Bld.fvar (← resolveFreeVar "Sequence.append")) [prefixSeq, suffixSeq]
      | _ => mkFallback
    else if fnameStr == "Seq_lib_map" || fnameStr == "Seq_lib_map_values" then
      -- `Seq::map` / `Seq::map_values` would otherwise pass a closure into the
      -- uninterpreted `Seq_lib_map`, which Strata's SMT encoder rejects.
      -- Synthesize an int-recursive replacement instead (see
      -- `emitSeqMapDecls`).  Fall back to the lambda form when the call
      -- doesn't match the expected shape, or when the closure captures an
      -- outer variable (which the standalone closure function couldn't see).
      match argsFiltered with
      | [seqArg, closureArg] =>
        -- VLIR drops `.Call` type arguments, so the closure's result type
        -- comes from the `Box` wrapper's `SpecFn` type (or, failing that,
        -- the element type of the call's expected sequence type).
        let closureRetTy? : Option Typ :=
          boxedClosureRetTy? closureArg <|> (expected?.bind seqElemTyp?)
        match peelCallWrappers closureArg with
        | .Bind (.Lambda closureParams) closureBody =>
          let paramNames := closureParams.map Prod.fst
          let captures := (expVarRefs closureBody).filter
            (fun v => !paramNames.contains v)
          let arityOk := closureParams.length == 1 || closureParams.length == 2
          match captures, closureRetTy?, closureParams.getLast?, arityOk with
          | [], some retTy, some (_, elemTy), true =>
            if isPrimitiveScalarTyp elemTy && isPrimitiveScalarTyp retTy then do
              let seqB ← expToBoole env bound none seqArg
              let closureBodyB ← withScope do
                addBoundVars
                  (closureParams.map (fun (n, _) => sanitizeVarName n)).toArray
                expToBoole (extendEnv env closureParams) closureParams.reverse
                  (some retTy) closureBody
              emitSeqMapDecls seqB closureBodyB closureParams elemTy retTy
            else mkFallback
          | _, _, _, _ => mkFallback
        | _ => mkFallback
      | _ => mkFallback
    else
      mkFallback
  | .CallLambda body args => do
    let fnExpr ← expToBoole env bound none body
    -- Recover the applied function's parameter types and push each onto the
    -- corresponding argument, so a widened argument (an erased `as int`/`as nat`
    -- over a bv value) coerces to the parameter type instead of reaching the
    -- lambda at the wrong numeric width.  Mirrors the parameter-typed argument
    -- lowering on the named-`Call` path; an argument past the recovered arity
    -- (or an unrecoverable function type) gets `none`, preserving plain lowering.
    let paramTys := ((inferComparableTyp? env bound body).bind specFnParamTyps?).getD []
    let args' ← args.zipIdx.mapM (fun (a, i) =>
      expToBoole env bound paramTys[i]? a)
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
    | .Quant q vars trigs => do
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      let (body', trigs') ← withScope do
        addBoundVars ((vars.map Prod.fst).map sanitizeVarName).toArray
        -- Translate the body before the triggers: `expToBoole` has side
        -- effects (fvar registration order via `resolveFreeVar`) that must
        -- not depend on whether this quantifier happens to carry a trigger,
        -- or non-triggered obligations' output could shift depending on
        -- unrelated trigger additions elsewhere in the program.
        let body' ← expToBoole env (vars.reverse ++ bound) (some .Bool) body
        -- Trigger expressions are arbitrary application terms (e.g. `f(i)`),
        -- not necessarily `Bool`, hence `expected? := none`. Translated in
        -- the same scope as the body so bound-variable references resolve
        -- identically.
        let trigs' ← trigs.toArray.mapM (fun grp =>
          grp.toArray.mapM (expToBoole env (vars.reverse ++ bound) none))
        pure (body', trigs')
      match q with
      | .Forall => return forallExprT binds trigs' body'
      | .Exists => return existsExprT binds trigs' body'
    | .Lambda vars => do
      -- When the outer context indicates an arrow type for the lambda
      -- (e.g. the lambda is the `f` argument of
      -- `Seq_lib_map<T,U>(s, f : int -> T -> U)`), thread the result
      -- type into the body's expected.  This is load-bearing for
      -- closures like `|i, x| x as nat`: Verus's VIR elides the
      -- spec-level `as nat` cast and lowers the body to just `Var x`
      -- with type `u64`, but Boole's types are strict (`bv64` ≠
      -- `nat`).  Without this hint the lambda emits `fun ... : bv64
      -- => x` returning `Sequence bv64`, and Strata rejects the call
      -- to `seq_as_nat_52 : Sequence nat -> nat` with `Impossible to
      -- unify ... nat with bv64`.  With the hint, the existing
      -- `.Var` coerceNumeric path at the body inserts the right cast.
      let bodyExpTy? : Option Typ :=
        expected?.bind fun ty =>
          match ty with
          | .SpecFn _ retTy => some retTy
          | _ => none
      let body' ← withScope do
        addBoundVars (vars.map Prod.fst).toArray
        expToBoole env (vars.reverse ++ bound) bodyExpTy? body
      let binds ← vars.toArray.mapM (fun (v, ty) => do
        let ty' ← typToBooleType ty
        pure (sanitizeVarName v, ty'))
      return lambdaExpr binds body'
    | .Choose _vars _pred =>
      -- Boole has no expression-level `choose`; the predicate is dropped
      -- here.  The shapes that occur in practice are handled upstream of this
      -- case: `let lhs = choose|v| pred(v)` statements become Boole
      -- `choose_assign` (`stmToBoole`'s `.Assign` arm), choose in
      -- call-argument position is hoisted to a `choose_assign` temporary
      -- (`hoistChooseArg`), and a spec fn whose whole body is a choose
      -- becomes Boole's native `command_choosefndef` (`specFnToBoole`).
      -- Fallback when reached elsewhere: translate the body verbatim.
      expToBoole env bound expected? body
  | .MatchBlock _scrut body =>
    expToBoole env bound expected? body
  | .ArrayLiteral elems => do
    let elemExpected? :=
      if expected?.map isSeqTyp |>.getD false then
        firstStructParamFromExpected? expected?
      else if expected?.bind arrayElemTyp? |>.isSome then
        expected?.bind arrayElemTyp?
      else
        none
    let args ← elems.mapM (expToBoole env bound elemExpected?)
    -- The element type is needed to pick the right `Sequence.empty_<T>`
    -- token.  Falling back to `.Empty` produces the untyped
    -- `Sequence.empty` name, which surfaces as a clean parser error if it
    -- ever fires (no element-type information was reachable).
    let elemTy := elemExpected?.getD .Empty
    if expected?.map isSeqTyp |>.getD false then
      seqLiteralExpr elemTy args
    else if expected?.bind arrayElemTyp? |>.isSome then
      seqLiteralExpr elemTy args
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

/-- The int-model meaning of `HasType τ e` for a numeric `τ`: the value of
    `e` (computed in unbounded int) lies in τ's value range.  Verus encodes
    exec overflow checks as exactly this shape — `assert HasType(u64, x*y)`
    followed by `assume HasType(u64, x*y)` and the clipped assignment — so
    these nodes carry the overflow verification conditions and the
    post-check range facts.  Returns `none` for types whose membership the
    Boole encoding enforces by typing alone (bool, datatypes, sequences,
    width-less `int`), which stay dropped. -/
private def hasTypeRangeCond (env : VarEnv) (t : Typ) (inner : Exp) :
    BuildM (Option BExpr) := do
  let range? : Option (Option Int × Option Int) :=
    match fixedWidthInfoOfTyp t with
    | some (w, false) => some (some 0, some ((2 : Int) ^ w - 1))
    | some (w, true)  => some (some (-((2 : Int) ^ (w - 1))), some ((2 : Int) ^ (w - 1) - 1))
    | none => if numKindOfTyp? t == some .nat then some (some 0, none) else none
  match range? with
  | none => pure none
  | some (lo?, hi?) =>
    let x ← expToBooleFlat env (some .Int) inner
    let conds := (lo?.map (fun lo => Bld.intLe (Bld.intConst lo) x)).toList ++
      (hi?.map (fun hi => Bld.intLe x (Bld.intConst hi))).toList
    match conds with
    | [c] => pure (some c)
    | [c1, c2] => pure (some (Bld.boolAnd c1 c2))
    | _ => pure none

/-- Lower a `decreases` clause (preserved on `ExecFn` / `ProofFn` as a list
    of `Stm.Assign decrease%initN := rhs`) into Boole's procedure-level
    `decr : Option Measure` slot.  Verus emits one Assign per source
    decreases term; we currently take the RHS of the first.  Lexicographic
    decreases (multiple terms) would need combining — deferred until the
    Boole side actually consumes `decr` (today it is captured but ignored
    as `_decr` in `Verify.lean`).  Returns `mkMeasure none` when the list
    is empty or shaped unexpectedly. -/
private def decreasesToMeasureAnn (env : VarEnv) (decreases : List Stm) :
    BuildM (StrataDDM.Ann (Option (BooleDDM.Measure SourceRange)) SourceRange) := do
  match decreases with
  | [] => pure (Bld.mkMeasure none)
  | (.Assign _ _ rhs _) :: _ =>
    let e ← expToBooleFlat env (some .Int) rhs
    pure (Bld.mkMeasure (some e))
  | _ :: _ => pure (Bld.mkMeasure none)

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

private def isUnitValueExp : Exp → Bool
  | .EnumCtor _ "tuple%0" [] => true
  | .TupleCtor 0 [] => true
  | _ => false

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
    let args ← (List.range size).mapM (fun i =>
      if i == field then pure rhs
      else tupleProjChain size i container)
    let updatedContainer ← tupleCtorChain args
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer
  | .Index base index, rhs => do
    let container ← lvalueReadExprToBoole env base
    let intIdx ← expToBoole env [] (some .Int) index
    let updatedContainer := Bld.seqUpdate container intIdx rhs
    lowerProjectedAssignRhsToRoot env projLayouts base updatedContainer

/-- Collect base-variable names that appear as the *container* argument of
    a `Std_specs_Core_index_set(container, index, value)` call anywhere in
    the body.  The translator's call-site lowering (in `stmToBoole`) rewrites
    these to `container := Sequence.update(container, index, value)`, so the
    mutation reaches the emitted Boole even though the source AST holds it
    as a `Stm.Call`, not a `Stm.Assign`.  Used both to identify by-value input
    parameters that need a shadow local, and to find fixed-size-array locals
    mutated inside a loop (which then need a `length` loop invariant). -/
partial def collectIndexSetTargets : Stm → List String
  | .Block stms => stms.flatMap collectIndexSetTargets
  | .If _ b1 b2 =>
    collectIndexSetTargets b1 ++ (b2.map collectIndexSetTargets).getD []
  | .Loop _ _ cond body _ _ =>
    (match cond with
      | some (s, _) => collectIndexSetTargets s
      | none => []) ++ collectIndexSetTargets body
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => collectIndexSetTargets s
  | .Call fn _ args =>
    if isIndexSetName fn || isVecIndexMutExecName fn then
      match args.head? with
      | some e => (vecVarFromExp e).toList
      | none => []
    else []
  | _ => []

/-! ## Statement Translation Main -/

/-- Hoist a `choose` expression in call-argument position
    (`lemma(i, choose|j| pred(j))`) to a fresh temporary bound by a
    `choose_assign` statement, returning the prelude statements and the
    temporary's name.  The temporary is added to the ambient scope: its
    inline `var` introduces a binding level, so the predicate here — and
    every expression of the enclosing call — must be translated with the
    temporary in scope or their variable indices shift by one.
    Multi-binder chooses are first normalized to the product form
    (`normalizeChooseProduct`); any other argument shape returns `none`
    and translates as a plain expression. -/
private def hoistChooseArg (env : VarEnv) (idx : Nat) (arg : Exp) :
    BuildM (Option (List BStmt × String)) := do
  if let .Bind (.Choose [(v, vTy)] pred) chooseBody :=
      normalizeChooseProduct (stripBoxWrappers arg) then
    if let .Var bodyVar := stripBoxWrappers chooseBody then
      if bodyVar == v then
        let tmpName := sanitizeVarName s!"{v}_choose_arg{idx}"
        let vTy' ← typToBooleType vTy
        addBoundVars #[tmpName]
        let pred' ← withScope do
          addBoundVars #[v]
          expToBooleFlat env (some .Bool) pred
        return some ([varStmt tmpName vTy',
          chooseAssignStmt tmpName (sanitizeVarName v) vTy' pred'], tmpName)
  return none

private def guardExclusiveBvForLoop (loopTy : Typ) (startExpr endExpr : BExpr)
    (loopStmt : BStmt) : BStmt :=
  match bitInfoOfTyp loopTy with
  | some (w, signed) =>
    -- Boole's `for ... to ...` limit is inclusive, so lowering Rust's
    -- exclusive `start..end` subtracts one from `end`.  In a bitvector domain
    -- that subtraction wraps for an empty range; guard the loop before forming
    -- an executable path through the wrapped limit.
    let nonempty :=
      if signed then bvSlt w startExpr endExpr else bvUlt w startExpr endExpr
    iteStmt nonempty #[loopStmt] #[]
  | none => loopStmt

mutual

partial def stmToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap)
    (retVar? : Option (String × Typ))
    (procName : String) :
    Stm → BuildM (List BStmt)
  | .Call fn _typArgs args => do
    if isGhostPervasiveCallName fn then
      return []
    -- `vec_index_mut` calls reach here already folded by
    -- `Normalize.inlineVecIndexMutWrites` into this same three-argument
    -- `(container, index, value)` shape, so they share the lowering.
    if isIndexSetName fn || isVecIndexMutExecName fn then
      match normalizeCallArgsForCallee env fn args with
      | [containerArg, indexArg, valueArg] =>
        match vecVarFromExp containerArg with
        | some baseName =>
          let some containerTy := env.get? baseName
            | throw s!"missing container type for index_set target {baseName}"
          let containerExpr ← expToBoole env [] (some containerTy) (unwrapViewCall containerArg)
          -- Sequence.update / Sequence.update-on-array expects an int
          -- index.  Forcing `expected? = some .Int` lets `expToBoole`'s
          -- Box / Var / Clip arms do the right coercion in one pass —
          -- the previous approach (translate with `none`, then post-coerce
          -- via `inferNumKind`) double-counted the type and round-tripped
          -- already-int loop counters through `bv64_to_int_u(int_to_bv64_u(...))`.
          let intIdx ← expToBoole env [] (some .Int) indexArg
          -- The stored value must land at the container's element type;
          -- without the expectation a bitwise value chain falls back to the
          -- default bv-usize width and mistypes the `Sequence.update`.
          let elemTy? := arrayElemTyp? containerTy <|> vecElemTyp? containerTy
            <|> seqElemTyp? containerTy
          let valueExpr ← expToBoole env [] elemTy? valueArg
          let updated ←
            match arrayElemTyp? containerTy with
            | some _ => pure (Bld.seqUpdate containerExpr intIdx valueExpr)
            | none =>
              let updateIdx ← resolveFreeVar "Sequence.update"
              pure (Bld.appN (Bld.fvar updateIdx) [containerExpr, intIdx, valueExpr])
          let containerTy' ← typToBooleType containerTy
          return [setStmtTyped containerTy' (sanitizeVarName baseName) updated]
        | none =>
          throw "unsupported index_set target without a recoverable base variable"
      | _ =>
        throw "unsupported index_set call shape"
    -- `Vec<T>` is represented by `Sequence T`, so executable push is the
    -- corresponding functional sequence append assigned back to the mutable
    -- argument.  The Verus SST supplies the Vec itself as argument 0 and the
    -- appended element as argument 1; the mutable-reference output is
    -- implicit in `Stm.Call`, so emitting an assignment here preserves it.
    if isVecPushExecName fn then
      match normalizeCallArgsForCallee env fn args with
      | [containerArg, valueArg] =>
        match vecVarFromExp containerArg with
        | some baseName =>
          let some containerTy := env.get? baseName
            | throw s!"missing container type for Vec::push target {baseName}"
          -- Unwrap a `view(v)` receiver, as the `index_set` arm above does:
          -- both operations take the container itself, and the view is the
          -- identity once `Vec` is `Sequence`.
          let containerExpr ←
            expToBoole env [] (some containerTy) (unwrapViewCall containerArg)
          -- A `Seq`-typed receiver is as valid here as a `Vec` one — both are
          -- `Sequence` after lowering — so fall back rather than refusing to
          -- translate the program.
          let elemTy? := vecElemTyp? containerTy <|> seqElemTyp? containerTy
          let valueExpr ← expToBoole env [] elemTy? valueArg
          let updated ← seqBuildExpr containerExpr valueExpr
          let containerTy' ← typToBooleType containerTy
          return [setStmtTyped containerTy' (sanitizeVarName baseName) updated]
        | none =>
          throw "unsupported Vec::push target without a recoverable base variable"
      | _ =>
        throw "unsupported Vec::push call shape"
    -- Other Vec_* and Slice_into_vec declarations are dropped at the
    -- decl-filter stage (see `declsToBooleProgram`).  Drop their remaining
    -- call sites too, so the emitted Boole has no dangling references.
    if isVec2SeqDroppedCalleeName fn then
      return []
    let argsFiltered := normalizeCallArgsForCallee env fn args
    let callee := identToBoole fn
    -- `choose` in argument position is hoisted to a `choose_assign`-bound
    -- temporary emitted before the call (`hoistChooseArg`).  Two passes:
    -- hoisting first registers every temporary's binding level, then all
    -- arguments — hoisted and plain — translate in that final scope.
    let mut hoistStmts : List BStmt := []
    let mut hoistedNames : Array (Option String) := #[]
    for (arg, idx) in argsFiltered.zipIdx do
      match ← hoistChooseArg env idx arg with
      | some (stmts, tmpName) =>
        hoistStmts := hoistStmts ++ stmts
        hoistedNames := hoistedNames.push (some tmpName)
      | none =>
        hoistedNames := hoistedNames.push none
    let mut argsBoole : List BExpr := []
    for (arg, idx) in argsFiltered.zipIdx do
      match hoistedNames[idx]? with
      | some (some tmpName) =>
        argsBoole := argsBoole ++ [← resolveVar tmpName]
      | _ =>
        let paramTy? := lookupFnParamTypeFull env callee idx
        argsBoole := argsBoole ++ [← expToBooleFlat env paramTy? arg]
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
    return hoistStmts ++ [callStmt (mutOuts.toArray) callee (argsBoole.toArray)]
  | .Assert exp | .AssertLean exp => do
    match exp with
    | .Unary (.HasType t) inner =>
      -- Verus materializes exec overflow checks as `assert HasType(τ, e)`
      -- ("possible arithmetic underflow/overflow"); numeric τ lowers to the
      -- range obligation, non-numeric τ is a typing tautology and drops.
      match ← hasTypeRangeCond env t inner with
      | some c => return [assertStmt "" c]
      | none => return []
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
    | .Unary (.HasType t) inner =>
      -- The companion of the overflow assert: Verus re-injects the checked
      -- range as `assume HasType(τ, e)` (also emitted for call results),
      -- which carries the `0 ≤ e < 2^w` facts the int model otherwise loses.
      match ← hasTypeRangeCond env t inner with
      | some c => return [assumeStmt "" c]
      | none => return []
    | _ =>
      let e ← expToBooleFlat env (some .Bool) exp
      return [assumeStmt "" e]
  | .Assign lhs lhsTy rhs _lhsIsInit => do
    if shouldDropAssignAsForLoopScaffolding lhs then
      return []
    if isUnitValueExp rhs then
      return []
    if let some lhsName := lvalueVarName? lhs then
      if let some elems := arrayLiteralElemsFromViewArg? rhs then
        let elemTy? :=
          if isSeqTyp lhsTy then firstStructParamFromExpected? (some lhsTy)
          else vecElemTyp? lhsTy
        if let some elemTy := elemTy? then
          let elems' ← elems.mapM (expToBoole env [] (some elemTy))
          let rhs' ← seqLiteralExpr elemTy elems'
          let lhsTy' ← typToBooleType lhsTy
          return [setStmtTyped lhsTy' (sanitizeVarName lhsName) rhs']
    let rhsCore := peelCallWrappers rhs
    -- `let lhs = choose|v| pred(v)` lowers to Boole's `choose_assign`
    -- statement (`lhs := choose v : T :: pred;`).  The Verus AST for this
    -- shape is `Bind (Choose [(v, ty)] pred) (Var v)` after wrappers are
    -- stripped; we recognise it here rather than letting the expression
    -- path drop the predicate.  A multi-binder choose-let arrives here as
    -- the tuple temporary's assignment (`tmp := choose|i, j| pred` with the
    -- binder tuple as the chosen value; the destructure is separate `Proj'`
    -- assignments) and is first normalized to a single binder over the
    -- product type (`normalizeChooseProduct`).
    if let some lhsName := lvalueVarName? lhs then
      if let .Bind (.Choose [(v, vTy)] pred) (.Var bodyVar) := normalizeChooseProduct rhsCore then
        if v == bodyVar then
          let vTy' ← typToBooleType vTy
          let pred' ← withScope do
            addBoundVars #[v]
            expToBooleFlat env (some .Bool) pred
          return [chooseAssignStmt (sanitizeVarName lhsName) (sanitizeVarName v) vTy' pred']
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
      -- Recognized Vec/Seq/Slice operations whose result is a pure
      -- expression: length, index, view, and empty-vector construction
      -- (`Vec::new`/`Vec::with_capacity`).  These must be handled *before*
      -- the `isVec2SeqDroppedCalleeName` drop below — names like `Vec_len`
      -- and `Vec_new` also match that broad `Vec_*` pattern, so dropping
      -- first would leave the LHS unconstrained (an arbitrary length/value)
      -- instead of the intended sequence expression.
      if isViewName fnName || isSeqLenSpecName fnName
            || isVecLenSpecName fnName || isVecLenExecName fnName
            || isVecIndexSpecName fnName || isVecIndexExecName fnName
            || isArrayIndexGetName fnName || isArrayFillForCopyTypesName fnName
            || isSliceLenSpecName fnName || isSliceLenExecName fnName
            || isSliceIndexGetName fnName || isWrappingAddName fnName
            || isVecNewExecName fnName || isVecWithCapacityExecName fnName then
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
      if isVecFromElemExecName fnName then
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
      if isUnitLikeTyp lhsTy then
        return []
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
    | some l => return [exitStmt (sanitizeIdent l)]
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
    -- `Loop.cond` has already been populated upstream by `normalizeBody`,
    -- which both hoists a body-prefix guard (`extractLoopGuardFromBody`) and
    -- inlines a cond block's guard temporary into the expression
    -- (`collectCondGuardSubsts`), so the expression is ready to lower here.
    let loopLabel? ← do
      match label with
      | some l => pure (some (sanitizeIdent l))
      | none =>
        let condNeeds := match cond with | some (s, _) => hasUnlabeledLoopControl s | none => false
        if condNeeds || hasUnlabeledLoopControl body then
          pure (some (← implicitLoopLabel))
        else
          pure none
    let condExpr ←
      match cond with
      | some (_, e) => expToBooleFlat env (some .Bool) e
      | none => pure (boolConst true : BExpr)
    let invExprs ← invs.toArray.mapM (fun inv => expToBooleFlat env (some .Bool) inv.body)
    -- (SynthConfig.loopLowerBound) A `usize` counter is non-negative by
    -- construction, but `IntPromotion` retypes index-only counters as `Int`
    -- and the loop havocs them, so `0 <= i` is lost at the loop boundary and
    -- every `s[i]` obligation fails on its lower-bound half.  Re-pin it,
    -- skipping any counter a source invariant already states.  Appended, so
    -- existing invariants keep their obligation indices.
    --
    -- Restricted to promoted-unsigned locals that the loop modifies *and* that
    -- its guard reads.  An invariant must also hold on entry, and a local
    -- declared inside the body (an inner loop's counter, say) has no value
    -- there — pinning `0 <= j` on the enclosing loop would assert something
    -- about an uninitialized variable.  Reading a local in the guard means
    -- Rust's definite-assignment rule already ran, so it holds a value at
    -- entry.
    let invExprs ← do
      if !(← getSynthConfig).loopLowerBound then pure invExprs
      else
        let condVars := match cond with
          | some (_, e) => expVarRefs e
          | none => []
        let modifiedNames :=
          ((collectSetVars body).map (·.name) ++ collectIndexSetTargets body).eraseDups
        modifiedNames.foldlM (fun acc v => do
          if condVars.contains v && (← isPromotedUnsignedLocal v) &&
              !invs.any (fun inv => statesNonNegOf v inv.body) then
            pure (acc.push (Synth.nonNegFact (← resolveVar v)))
          else pure acc) invExprs
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
    -- Decide whether the for-loop binder should be retyped as `Int`.
    -- The `IntPromotion` pass populates `BuildCtx.promotedLocals` at
    -- procedure entry with the names it judged safe to promote based
    -- on actual use-sites.  A binder ends up there iff every use is in
    -- a sequence-index / length-comparison / int-arith position and at
    -- least one use is a qualifying (sequence-index or length-compare)
    -- one.  Bv-specific uses inside the body get an `int_to_bv*_u`
    -- cast on the other end via `coerceNumeric`.
    let promote ← isPromotedLocal loop.loopVarName
    let loopBinderTy : Typ :=
      if promote then .Int else loop.loopVarTy
    let loopVarTy ← typToBooleType loopBinderTy
    let loopVarSan := sanitizeVarName loop.loopVarName
    let startExpr ← expToBooleFlat env (some loopBinderTy) loop.startExp
    let endE ← expToBooleFlat env (some loopBinderTy) loop.endExp
    let limitExpr ← match bitWidthOfTyp loopBinderTy with
      | some w => pure (bvSub w endE (bitvecConstNat w 1))
      | none => pure (intSub endE (intConst 1))
    -- Make the binder's int type visible to body translation: `Var i`
    -- look-ups in `inferBitInfo` / `inferComparableTyp?` consult `env`,
    -- so without the entry the body can't drive `bv*-to-int` cast
    -- decisions correctly.
    let envWithBinder := extendEnv env [(loop.loopVarName, loopBinderTy)]
    let (invExprs, measureExpr?, bodyStms) ← withScope do
      pushBoundVar loopVarSan
      let userInvs ← loop.invariants.toArray.mapM (fun inv =>
        expToBooleFlat envWithBinder (some .Bool) inv.body)
      let cfg ← getSynthConfig
      -- (SynthConfig.loopLowerBound) Verus's `for i in lo..hi` iterator
      -- guarantees `lo <= i` throughout, but Strata's `for i := lo to hi` hands
      -- the body only the *upper* bound `i <= hi` (via the guard); without
      -- `lo <= i` every `s[i]` out-of-bounds obligation fails on its `0 <= i`
      -- half (repro: `assert i < hi` passes but `assert 0 <= i` is unknown).
      -- Lowered from the source comparison `startExp <= loopVar` so the int/bv
      -- dispatch and loop-variable scoping run through `expToBooleFlat`, as for
      -- a user invariant.  Appended (not prepended) so existing invariants keep
      -- their obligation indices.
      let invsWithBound ← if cfg.loopLowerBound then do
          let lb ← expToBooleFlat envWithBinder (some .Bool)
            (Synth.lowerBoundInvExp loop.startExp loop.loopVarName)
          pure (userInvs.push lb)
        else pure userInvs
      -- (SynthConfig.fixedArrayLengths) Fixed-size-array vars *mutated inside*
      -- the loop (via `arr[i] = …`, lowered to `arr := Sequence.update(arr,…)`,
      -- or a plain reassign) are havoc'd by the loop, dropping the entry
      -- `length == N` fact.  Re-pin it as a loop invariant for each such array
      -- (`Sequence.update` preserves length, so it is maintained).  Read-only
      -- arrays keep their entry fact; restricting to *modified* vars also avoids
      -- pinning a local whose length isn't established until after this loop.
      let lenInvs ← if cfg.fixedArrayLengths then do
          let modifiedNames :=
            ((collectSetVars (.Block loop.userBody)).map (·.name)
              ++ collectIndexSetTargets (.Block loop.userBody)
              ++ collectProjectedAssignBases (.Block loop.userBody)).eraseDups
          modifiedNames.filterMapM fun v =>
            match (envWithBinder.get? v).bind arrayFixedLen? with
            | some n => do
              let vExpr ← resolveVar v
              pure (some (Synth.fixedArrayLenFact vExpr n))
            | none => pure none
        else pure ([] : List BExpr)
      let invExprs := invsWithBound ++ lenInvs.toArray
      -- Lower the first source `decreases` term into the for-loop's
      -- measure slot.  Lexicographic decreases (multiple terms) collapse
      -- to the head — combining them is future work.  Skip clauses whose
      -- head is a `Pervasive_ghost_*` call, which is how Verus shapes the
      -- auto-synthesized decrease for an iterator without an explicit
      -- source clause:
      --   `if isSome(Pervasive_ghost_decrease(iter))
      --       then Option_Some_0(...) else Pervasive_arbitrary`
      -- That expression references iterator scaffolding that isn't in
      -- our prelude; lowering it would surface as an unresolved fvar.
      let measureExpr? ← match loop.decrease.head? with
        | some e =>
          if expContainsGhostPervasiveCall e || ForLoop.expRefsVERUSVar e then pure none
          else do
            let ce0 ← expToBooleFlat envWithBinder none e
            let srcKind? := inferNumKind envWithBinder [] e
            let ce ← coerceNumeric srcKind? (some .int) ce0
            pure (some ce)
        | none => pure none
      let bodyStms ← stmToBoole envWithBinder projLayouts mutArgMap retVar? procName (Stm.Block loop.userBody)
      pure (invExprs, measureExpr?, bodyStms)
    let loopStmt := forToStmt loopVarSan loopVarTy startExpr limitExpr
      measureExpr? invExprs bodyStms.toArray
    let loopStmt := guardExclusiveBvForLoop loopBinderTy startExpr endE loopStmt
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
    -- An `assert X; assume X` pair from Verus's SST is kept whole: Strata's
    -- `assert` defers the obligation without extending the path conditions
    -- (`Imperative/CmdEval`), so the `assume` is what carries the checked
    -- fact to subsequent obligations.
    if isTrivialTrueAssert a && isQueryScaffoldingAssume e next then
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
      if isTrivialTrueAssert a then
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

/-- A user-defined datatype (struct or enum) — the parameter shape that makes a
    `decreases` measure *structural* rather than int-valued.  `Boxed`/`Datatype`
    references parse to `.Struct` (`Typ.fromJson`); decorations are peeled. -/
private def isStructuralMeasureTyp : Typ → Bool
  | .Struct _ _ => true
  | .Enum _ _ => true
  | .Decorated _ t => isStructuralMeasureTyp t
  | _ => false

/-- Index of the parameter to mark `@[cases]` for a recursive spec fn whose
    `decreases` measure is a parameter of user-datatype type.  Strata classifies
    a datatype-valued measure as structural recursion and requires the
    decreasing parameter to carry `@[cases]`; int-valued measures do not, and
    keep their `decreases` clause.  Reuses the parser's `recursiveCasesIdxHint`
    (the decreasing-parameter index, with `Box`/`HasType` wrappers already
    peeled) and gates it on the parameter being a datatype — mirroring
    `getDecreasesKind` in Strata's `Transform/TerminationCheck.lean`. -/
private def structuralCasesParamIdx? (f : SpecFn) : Option Nat :=
  match f.recursiveCasesIdxHint with
  | some idx =>
    match f.inputs[idx]? with
    | some (_, ty) => if isStructuralMeasureTyp ty then some idx else none
    | none => none
  | none => none

private def mkMonoInputs (inputs : List (String × Typ)) (casesIdx? : Option Nat := none) :
    BuildM (BooleDDM.Bindings SourceRange × Array String) := do
  let mut bindings : Array (BooleDDM.Binding SourceRange) := #[]
  let mut names : Array String := #[]
  let mut i := 0
  for (name, ty) in inputs do
    let sanName := sanitizeVarName name
    let ty' ← typToBooleType ty
    -- Mark the structural-recursion parameter `@[cases]` (see
    -- `structuralCasesParamIdx?`); Strata requires it for datatype-measured
    -- recursion. All other parameters use the plain binding.
    let binding :=
      if casesIdx? == some i then
        BooleDDM.Binding.casesBinding default (ann sanName) (BooleDDM.TypeP.expr ty')
      else
        BooleDDM.Binding.mkBinding default (ann sanName) (BooleDDM.TypeP.expr ty')
    bindings := bindings.push binding
    names := names.push sanName
    i := i + 1
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

/-- Like `expContainsLambda`, but ignores the closure argument of a
    `Seq::map` / `Seq::map_values` call.  Those closures are lowered by
    `emitSeqMapDecls` into ordinary recursive declarations with no surviving
    lambda; and on the fallback path the lambda lands inside the
    uninterpreted `Seq_lib_map`, where the `inline` attribute cannot help
    either.  Either way such a closure must not force the enclosing spec
    function to be inlined. -/
partial def expHasInlineForcingLambda : Exp → Bool
  | .Const _ _ | .Var _ => false
  | .Call fn _ args =>
    let callee := identToBoole (CallFun.name fn)
    if callee == "Seq_lib_map" || callee == "Seq_lib_map_values" then
      -- Recurse into every argument except the trailing closure.
      args.dropLast.any expHasInlineForcingLambda
    else args.any expHasInlineForcingLambda
  | .CallLambda body args =>
    expHasInlineForcingLambda body || args.any expHasInlineForcingLambda
  | .StructCtor _ fields => fields.any (fun (_, e) => expHasInlineForcingLambda e)
  | .EnumCtor _ _ data => data.any (fun (_, e) => expHasInlineForcingLambda e)
  | .TupleCtor _ data => data.any expHasInlineForcingLambda
  | .Unary _ e => expHasInlineForcingLambda e
  | .Binary _ a b => expHasInlineForcingLambda a || expHasInlineForcingLambda b
  | .If c t f =>
    expHasInlineForcingLambda c || expHasInlineForcingLambda t
      || expHasInlineForcingLambda f
  | .Bind (.Lambda _) _ => true
  | .Bind (.Let _ _ e) body =>
    expHasInlineForcingLambda e || expHasInlineForcingLambda body
  | .Bind (.Quant _ _ trigs) body =>
    trigs.any (·.any expHasInlineForcingLambda) || expHasInlineForcingLambda body
  | .Bind (.Choose _ pred) body =>
    expHasInlineForcingLambda pred || expHasInlineForcingLambda body
  | .ArrayLiteral elems => elems.any expHasInlineForcingLambda
  | .MatchBlock (scrut, _) body =>
    expHasInlineForcingLambda scrut || expHasInlineForcingLambda body

/-- Strip `Decorated` wrappers to expose the underlying type. -/
private def stripTypDecoration : Typ → Typ
  | .Decorated _ ty => stripTypDecoration ty
  | ty => ty

/-- If `ty` is a single-field `[T; N]` wrapper struct (modeled as a transparent
    `Sequence T` synonym), the `(destructor Boole name, length)` recorded by the
    `wrapperInfo` pre-pass; else none. -/
def wrapperLenInfo? (ty : Typ) : BuildM (Option (String × Nat)) := do
  match stripTypDecoration ty with
  | .Struct name _ => pure ((← get).wrapperInfo.get? (datatypeNameOf name))
  | _ => pure none

/-- `Sequence.length(<destructor>(x)) == n` — the wrapper's length stated in the
    body's own vocabulary (the destructor applied to the wrapper value).  Stating
    it on `<destructor>(x)` rather than `x` matches how bodies index the wrapper
    (`Sequence.select(<destructor>(x), i)`), so a strict (non-unfolding) SMT
    solver discharges the bound by syntactic match.  Same shape as the struct
    field length axiom, minus the `forall`. -/
def wrapperLenFact (x : BExpr) (dtorName : String) (n : Nat) : BuildM BExpr := do
  let dtorIdx ← resolveFreeVar dtorName
  pure (Synth.fixedArrayLenFact (Bld.appN (Bld.fvar dtorIdx) [x]) n)

/-- Substitute type parameters by name.  Instantiates an enum variant's
    declared payload type at the use site's type arguments
    (`Option_option edwardsPoint`: the `Some` payload `V` becomes
    `edwardsPoint`). -/
private partial def substTypParams (subst : List (String × Typ)) : Typ → Typ
  | .TypParam i => ((subst.lookup i).getD (.TypParam i))
  | .Tuple t1 t2 => .Tuple (substTypParams subst t1) (substTypParams subst t2)
  | .Array t len? => .Array (substTypParams subst t) len?
  | .SpecFn ps ret => .SpecFn (ps.map (substTypParams subst)) (substTypParams subst ret)
  | .Decorated d t => .Decorated d (substTypParams subst t)
  | .Struct n ps => .Struct n (ps.map (substTypParams subst))
  | .Enum n ps => .Enum n (ps.map (substTypParams subst))
  | t => t

/-- Length facts for every array-backed component reachable from `expr : ty`
    through selectors.  `[T; N]` yields `Sequence.length(<path>) == N`; a
    wrapper yields the fact on its destructor; a tuple recurses into both
    slots (`(A, B, C)` is right-nested, so paths are `Tuple2.._0`/`.._1`
    chains); a monomorphic single-constructor struct recurses through its
    field selectors (`fieldElement51..limbs(edwardsPoint..X(p))`); an enum
    recurses through each variant's payload selectors with the fact guarded
    by the variant tester (`isSome(x) ==> length(…(Some_0(x))) == 5`).
    `visited` cuts cycles in recursive datatypes.  Stated per boundary as
    requires/ensures — datatypes are total, so a global `forall s : <dt>`
    length axiom would be unsound (`s` ranges over constructor applications
    of arbitrary sequences). -/
partial def componentLenFacts (ty : Typ) (expr : BExpr)
    (visited : List String := []) : BuildM (List BExpr) := do
  match arrayFixedLen? ty with
  | some n => return [Synth.fixedArrayLenFact expr n]
  | none =>
    match (← wrapperLenInfo? ty) with
    | some (dtor, n) => return [← wrapperLenFact expr dtor n]
    | none =>
      match stripTypDecoration ty with
      | .Tuple t1 t2 =>
        let fstIdx ← resolveFreeVar tupleFstSelector
        let sndIdx ← resolveFreeVar tupleSndSelector
        let fsts ← componentLenFacts t1 (Bld.appN (Bld.fvar fstIdx) [expr]) visited
        let snds ← componentLenFacts t2 (Bld.appN (Bld.fvar sndIdx) [expr]) visited
        return fsts ++ snds
      -- Datatype references parse as `.Struct` whether the declaration is a
      -- struct or an enum; try both layout maps.
      | .Struct name args | .Enum name args =>
        let dtName := datatypeNameOf name
        if visited.contains dtName then return []
        match (← get).structFieldInfo.get? dtName with
        | some fields =>
          fields.foldlM (fun acc (fname, fty) => do
            let selIdx ← resolveFreeVar (datatypeDestructorNameOf name fname)
            let facts ← componentLenFacts fty (Bld.app (Bld.fvar selIdx) expr)
              (dtName :: visited)
            pure (acc ++ facts)) []
        | none =>
        match (← get).enumFieldInfo.get? dtName with
        | none => return []
        | some (tyParams, variants) =>
          if tyParams.length != args.length then return []
          let subst := tyParams.zip args
          variants.foldlM (fun acc (vname, fields) => do
            if fields.isEmpty then pure acc else do
            let testerIdx ← resolveFreeVar (enumTesterNameOf name vname)
            let guard := Bld.app (Bld.fvar testerIdx) expr
            let inner ← fields.foldlM (fun acc2 (fkey, fty) => do
              -- The selector is `<dt>..<binding>`; `projFieldNameOf` gives
              -- the binding name the declaration uses.
              let selIdx ← resolveFreeVar
                s!"{dtName}..{projFieldNameOf name vname fkey}"
              let facts ← componentLenFacts (substTypParams subst fty)
                (Bld.app (Bld.fvar selIdx) expr) (dtName :: visited)
              pure (acc2 ++ facts)) []
            pure (acc ++ inner.map (Bld.boolImplies guard ·))) []
      | _ => return []

/-- `componentLenFacts`, except that a directly `[T; N]`-typed binding yields
    nothing — those get their length from the `fixedArrayLenElts` sites. -/
def boundaryLenFacts (ty : Typ) (expr : BExpr) : BuildM (List BExpr) :=
  if (arrayFixedLen? ty).isSome then pure [] else componentLenFacts ty expr

/-- Length contracts for wrapper- and tuple-typed bindings: a `requires` per
    input fact, an `ensures` per output fact (`boundaryLenFacts`).  Every fn
    boundary carries the facts, so callers discharge their `_calls_`
    obligations from the matching `ensures`.  Emit these before the user
    spec: each spec clause's definedness is checked with only the preceding
    clauses assumed.  Must run in the scope where the bindings resolve. -/
def wrapperLenSpecElts (inputs outputs : List (String × Typ)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  if !(← getSynthConfig).fixedArrayLengths then return #[]
  let mut elts : Array (BooleDDM.SpecElt SourceRange) := #[]
  for (name, ty) in inputs do
    for fact in (← boundaryLenFacts ty (← resolveVar name)) do
      elts := elts.push (.requires_spec default noLabel (ann none) fact)
  for (name, ty) in outputs do
    for fact in (← boundaryLenFacts ty (← resolveVar name)) do
      elts := elts.push (.ensures_spec default noLabel (ann none) fact)
  return elts

/-- One `Sequence.length(binding) == N` spec elt per direct `[T; N]` binding,
    wrapped by `mkElt` (requires or ensures, per call site). -/
def fixedArrayLenElts (mkElt : BExpr → BooleDDM.SpecElt SourceRange)
    (binds : List (String × Typ)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  if !(← getSynthConfig).fixedArrayLengths then return #[]
  binds.foldlM (fun acc (name, ty) => do
    match arrayFixedLen? ty with
    | some n =>
      let e ← resolveVar name
      pure (acc.push (mkElt (Synth.fixedArrayLenFact e n)))
    | none => pure acc) #[]

/-- Unlabeled `requires`/`ensures` constructors for synthesized facts. -/
private def mkLenReq (fact : BExpr) : BooleDDM.SpecElt SourceRange :=
  .requires_spec default noLabel (ann none) fact
private def mkLenEns (fact : BExpr) : BooleDDM.SpecElt SourceRange :=
  .ensures_spec default noLabel (ann none) fact

/-- `requires Sequence.length(p) == N` per direct `[T; N]` input.  A
    `requires`, not just a body entry-`assume`, because spec-clause
    definedness cannot see the body: a later requires/ensures reading the
    param needs the length as an earlier clause.  Callers discharge the
    resulting obligation from the threaded boundary facts. -/
def fixedArrayParamReqElts (inputs : List (String × Typ)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) :=
  fixedArrayLenElts mkLenReq inputs

/-- Length `requires` for a spec fn's parameters, shared by the non-mutual
    (`specFnToBoole`) and mutual-recursive paths.  Direct `[T; N]` params get
    `Sequence.length(p) == N` (`fixedArrayParamReqElts`); wrapper and tuple
    params get their facts prepended (`wrapperLenSpecElts`). -/
def specFnParamLenElts (inputs : List (String × Typ))
    (elts : Array (BooleDDM.SpecElt SourceRange)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  if !(← getSynthConfig).fixedArrayLengths then return elts
  pure ((← wrapperLenSpecElts inputs []) ++ elts ++ (← fixedArrayParamReqElts inputs))

/-- Append a bodied spec fn's `recommends` as `requires`.  Verus treats them
    as unchecked hints, but Boole checks the body's definedness and needs them
    (e.g. an index bound guarding a `Sequence.select`).  Placed after the
    length requires so their own definedness sees the params' lengths.
    Body-less fns skip them: no body to check, only extra call-site
    obligations. -/
def specFnRecommendsElts (envLocal : VarEnv) (f : SpecFn)
    (elts : Array (BooleDDM.SpecElt SourceRange)) :
    BuildM (Array (BooleDDM.SpecElt SourceRange)) := do
  if f.body.isNone then return elts
  f.recommends.foldlM (fun acc r => do
    pure (acc.push (mkLenReq (← expToBooleFlat envLocal (some .Bool) r)))) elts

/-- Defining axiom for a recursive spec function: `∀ params :: f(params) == body`.

    Strata writes such an axiom itself for a function that recurses structurally
    on a datatype (those carry `@[cases]`), but not for one that recurses on a
    plain `int`/`nat` measure — its SMT encoder leaves those as functions with no
    axiom at all.  Nothing then relates `f` at one argument to `f` at another, so
    a proof that inducts on the function's own recursion cannot go through however
    much the caller asserts.  That is what leaves the Lagrange-interpolation range
    lemmas unproved in the Shamir benchmark.

    Stating the definition is the standard way to give a recursive function
    meaning in SMT, and it is sound because termination has already been checked:
    Verus rejects a non-terminating spec function long before export.  The cost is
    solver time — an axiom like this can be expensive to instantiate — which is
    bounded by the existing per-obligation limits and cannot turn a failing proof
    into a passing one.

    `body` is reused exactly as the function's own declaration built it, under the
    same input binders and with nothing else in scope, so its variable indices
    already line up with the binders introduced here. -/
private def recFnUnfoldingAxiom (fnName : String) (inputs : List (String × Typ))
    (body : BExpr) : BuildM BCmd := do
  let fnIdx ← resolveFreeVar fnName
  let k := inputs.length
  let argBvars := (List.range k).map (fun i => Bld.bvar (k - 1 - i))
  let lhs := if k == 0 then Bld.fvar fnIdx else Bld.appN (Bld.fvar fnIdx) argBvars
  let eqExpr := Bld.eq lhs body
  let axiomExpr ← if k == 0 then pure eqExpr else do
    let binders ← inputs.toArray.mapM (fun (x, ty) => do
      pure (sanitizeVarName x, ← typToBooleType ty))
    pure (forallExpr binders eqExpr)
  return .command_axiom default (someLabel s!"{fnName}_unfold") axiomExpr

def specFnToBoole (env : VarEnv) (emitBody : Bool) (f : SpecFn) : BuildM (List BCmd) := do
  -- An `arbitrary()` body lowers as declaration-only (`exprIsBareArbitrary`):
  -- same semantics (unspecified value), no dangling `Pervasive_arbitrary`.
  let f := if f.body.any exprIsBareArbitrary then { f with body := none } else f
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  -- A datatype-valued `decreases` measure marks the decreasing parameter
  -- `@[cases]` for structural recursion (Strata requires it; int-valued
  -- measures keep their `decreases` clause instead).
  let casesIdx? := if f.isRecursive then structuralCasesParamIdx? f else none
  let (inputBindings, inputNames) ← mkMonoInputs f.inputs casesIdx?
  let outputTy ← typToBooleType f.returnType
  let envLocal := extendEnv env f.inputs
  -- A spec fn whose whole body is `choose |v| pred` (Verus's Hilbert choice)
  -- has no Boole *expression* form, but Strata's `command_choosefndef` (#1365)
  -- declares exactly this shape: `function f(args) : R := choose v : T :: pred;`.
  -- Emit it directly so choose-defined spec fns translate 1:1.
  --
  -- Soundness note: Strata lowers `command_choosefndef` to an *unguarded*
  -- choice axiom (`∀ args, v :: v = f(args) ==> pred`, i.e.
  -- `∀ args :: pred[v := f(args)]`).  That is a conservative extension only for
  -- predicates with a witness at every argument; a predicate unsatisfiable at
  -- some argument makes the context inconsistent there.  The Verus spec fns we
  -- translate choose over satisfiable predicates (e.g. `u8_32_from_nat`: every
  -- `n mod 2^256` has a 32-byte encoding), and the general guard belongs in
  -- Strata's lowering (requested on #1365), not in per-frontend axioms.
  if emitBody then
    if let some bodyExp := f.body then
    if let .Bind (.Choose [(v, vTy)] pred) chooseBody :=
        normalizeChooseProduct (stripBoxWrappers bodyExp) then
      if let .Var bodyVar := stripBoxWrappers chooseBody then
      if bodyVar == v then
        -- `pred` translated under the (params, v) de Bruijn context the
        -- construct's scope chain expects (v = bvar 0, innermost param =
        -- bvar 1, …), with a fixed-size-array binder's `Sequence.length == N`
        -- fact folded in so the chosen value carries its `[T; N]` binder type.
        return ← withScope do
          addBoundVars inputNames
          let predB ← withScope do
            addBoundVars #[v]
            expToBoole envLocal [(v, vTy)] (some .Bool) pred
          let vRef ← withScope do
            addBoundVars #[v]
            expToBoole envLocal [(v, vTy)] none (.Var v)
          let predFull := match arrayFixedLen? vTy with
            | some n => Bld.boolAnd (Synth.fixedArrayLenFact vRef n) predB
            | none => predB
          let vTyB ← typToBooleType vTy
          let vBind := BooleDDM.MonoBind.mono_bind_mk default
            (ann (sanitizeVarName v)) vTyB
          pure [.command_choosefndef default name typeArgs inputBindings
            outputTy vBind predFull]
  let (body?, specElts, decrAnn) ← withScope do
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
    -- Fixed-array length `requires` for `[T; N]` and wrapper-struct params,
    -- then the `recommends` domain conditions — both shared with the
    -- mutual-recursive spec-fn path.
    let elts ← specFnParamLenElts f.inputs elts
    let elts ← specFnRecommendsElts envLocal f elts
    -- Lower Verus's serialized `decreases` measure (parsed into
    -- `SpecFn.decreases`) for recursive spec fns.  The termination-check
    -- body is a `Block` whose first stmt is `decrease%init0 := <measure>`;
    -- `decreasesToMeasureAnn` extracts that RHS.  Lowered inside this
    -- input-bound scope since the measure names the params.  Falls back to
    -- `mkMeasure none` (Strata's own checker) on unexpected shapes.
    let decrAnn ←
      -- `@[cases]` supplies the structural measure (Strata's adtRank), so the
      -- datatype-valued `decreases` is dropped rather than emitted into the
      -- int-valued measure slot.
      if casesIdx?.isSome then pure (Bld.mkMeasure none)
      else match f.decreases with
        | some (.Block stmts) => decreasesToMeasureAnn envLocal stmts
        | some s => decreasesToMeasureAnn envLocal [s]
        | none => pure (Bld.mkMeasure none)
    pure (body?, elts, decrAnn)
  match body? with
  | some body =>
    if f.isRecursive then
      -- Emit Verus's `decreases` measure into Strata's `recfn_decl` slot
      -- (was previously dropped to `none` per `[CORE-decreases]`, leaving
      -- Strata's auto checker unable to prove sequence-recursion
      -- termination, e.g. `bytes_seq_as_nat` recursing on `Seq::subrange`).
      -- Note: `recfn_decl` has no inline slot upstream, so a lambda-bearing
      -- recursive spec fn cannot be auto-inlined here; it would hit
      -- Strata's SMT encoder lambda-rejection.  Tracked separately.
      let recDecl :=
        BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy
          (ann specElts) decrAnn body
      let recCmd : BCmd := .command_recfndefs default (ann #[recDecl])
      -- (SynthConfig.recFnUnfold) A `@[cases]` function already gets its
      -- defining axiom from Strata; only plain-measure recursion needs one here.
      if casesIdx?.isNone && (← getSynthConfig).recFnUnfold then
        let unfoldAxiom ← recFnUnfoldingAxiom fnName f.inputs body
        pure [recCmd, unfoldAxiom]
      else
        pure [recCmd]
    else
      -- Auto-inline lambda-bearing spec functions.  Strata's SMT encoder
      -- can't axiomatize a function whose body contains an unapplied
      -- lambda (`Cannot encode function 'foo' to SMT: its body contains
      -- a lambda expression. Consider marking the function as `inline``);
      -- emitting `inline function ...` makes Strata substitute the body
      -- at each call site, where the lambda typically beta-reduces under
      -- `Seq_lib_map`/`Seq_lib_filter`-style builtins before SMT
      -- encoding.  This is semantically equivalent to the axiomatic
      -- definition Strata would otherwise generate.
      -- `Seq::map` closures are excluded: they are synthesized into
      -- recursive declarations (`emitSeqMapDecls`), so they leave no
      -- lambda in the translated body.
      let shouldInline := f.body.any expHasInlineForcingLambda
      let inlineAnn :=
        if shouldInline then ann (some (.inline default)) else ann none
      pure [.command_fndef default name typeArgs inputBindings outputTy
        (ann specElts) body inlineAnn]
  | none =>
    pure [.command_fndecl default name typeArgs inputBindings outputTy]

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
  -- Drop names that the recovered for-loop's binder declares inline (a
  -- separate `var i;` would conflict with the `for i := …` binder,
  -- producing "Variable i already in context").
  let localsAll := match bodyStm? with
    | some body => filterOutForLoopBinders body localsAll
    | none => localsAll
  -- Decide which `usize`/`isize` locals + for-loop binders to retype as
  -- `Int` (see `IntPromotion`).  Apply the rewrite to both the body and
  -- the locals list before translation; the for-loop arm reads the same
  -- set from BuildCtx.  ProofFn variant — no by-value mut shadowing
  -- happens here, so the body to inspect is `bodyStm?`.
  let promoted : Std.HashSet String :=
    match bodyStm? with
    | some body => IntPromotion.inferIntPromotableLocals localsAll body
    | none => ∅
  -- Read off signedness before the rewrite replaces the source types.
  let promotedUnsigned := IntPromotion.unsignedPromotedLocals promoted localsAll
  let localsAll := IntPromotion.rewriteLocalsForPromoted promoted localsAll
  let bodyStm? := bodyStm?.map (IntPromotion.rewriteBodyForPromoted promoted)
  let outputs := retDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body, decrAnn) ← withPromotedLocals promoted promotedUnsigned <| withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let userSpecElts ← mkSpecElts envLocal f.requires f.ensures []
    -- A `[T; N]` return carries `ensures Sequence.length(result) == N` to
    -- callers, mirroring the exec-fn return site.
    let arrayRetElts ← fixedArrayLenElts mkLenEns retDecls
    -- Synthesized length facts (wrapper/tuple bindings, `[T; N]` params) go
    -- before the user spec so its clauses' definedness checks can use them.
    -- The requires also serve as the body's entry facts, keeping the params'
    -- index accesses in-bounds.
    let specElts := (← wrapperLenSpecElts f.inputs retDecls)
      ++ (← fixedArrayParamReqElts f.inputs) ++ arrayRetElts ++ userSpecElts
    -- Lower the source-level `decreases` clause BEFORE body translation so
    -- the bound-var stack is in a known-clean state (just inputs+outputs).
    -- The body's internal scopes can otherwise leave the stack longer than
    -- this scope expects, producing dangling `bvar!N` indices in the
    -- decreases expression.
    let decrAnn ← decreasesToMeasureAnn envLocal f.decreases
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
    pure (specElts, body, decrAnn)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn decrAnn spec (ann (some body)))

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
  let seqSelectIdx ← resolveFreeVar "Sequence.select"
  let zeroInt := intConst 0
  let zeroBv := bitvecConstNat usizeBitWidth 0
  let oneBv := bitvecConstNat usizeBitWidth 1
  -- The empty seed matches the Vec element type captured from the procedure
  -- inputs; a polymorphic element type renders as `Sequence.empty<T>()`.
  let initEmptyExpr ← seqEmptyExpr elemTy
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
    let loopStmt := forToStmt loopVarName nTy' zeroBv limitExpr none
      #[invBounds, invLen, invElems] #[setStmtTyped retTy (sanitizeVarName f.retName) nextRet]
    pure (guardExclusiveBvForLoop nTy zeroBv nExpr loopStmt)
  pure (BooleDDM.Block.block default (ann #[initStmt, loopStmt]))

/-- Exec collection types whose length is a Rust `usize`: `Vec<T>` and
    dynamically-sized slices (`.Array t none`), through decorations (`&`,
    `&mut`, `Box`, …).  Spec `Seq<T>` is genuinely unbounded and deliberately
    does not match. -/
private partial def isUsizeLenSeqTyp : Typ → Bool
  | .Decorated _ t => isUsizeLenSeqTyp t
  | .Array _ none => true
  | t => (vecElemTyp? t).isSome

def execFnToBoole (env : VarEnv) (projLayouts : List ProjLayout) (mutArgMap : MutArgMap)
    (sfMap : SpecFnMap) (f : ExecFn) : BuildM BCmd := do
  let fnName := identToBoole f.name
  addFreeVars #[fnName]
  let name := ann fnName
  let typeArgs := mkTypeArgsAnn (fnTypeParams f.inputs f.returnType)
  let mutOutDecls :=
    f.inputs.filterMap (fun (n, t) =>
      (mutRefPayload? t).map (fun payloadTy => (n, s!"{n}_out", payloadTy)))
  -- By-value mutable parameters: Verus permits `mut p: T` for non-`&mut`
  -- parameters and the body assigns to them in place.  Strata's
  -- modifies-discipline rejects mutating an input parameter, so for every
  -- non-`&mut` input that the body assigns to we introduce a shadow local
  -- `<name>_local`, copy the parameter value at procedure entry, and
  -- rewrite all body references to the shadow name.  Parallels the
  -- `mutOutDecls` pattern used for `&mut` parameters.
  let mutRefInputNames := mutOutDecls.map (fun (n, _, _) => n)
  -- Names mutated by direct `Assign` LHS in the body.
  let assignedInBody := (collectSetVars f.body).map LocalDeclInfo.name
  -- Names mutated indirectly via `Std_specs_Core_index_set(container, …)`
  -- calls.  The translator rewrites these to `container := Sequence.update(…)`
  -- in `stmToBoole`, so the mutation appears in the emitted Boole even though
  -- `collectSetVars` doesn't see it in the source AST.
  let mutatedNames := assignedInBody ++ collectIndexSetTargets f.body
    ++ collectProjectedAssignBases f.body
  let byValMutDecls : List (String × String × Typ) :=
    f.inputs.filterMap (fun (n, t) =>
      if mutRefInputNames.contains n then none
      else if mutatedNames.contains n then
        some (n, s!"{n}_local", t)
      else none)
  let mutRenames :=
    mutOutDecls.map (fun (n, outName, _) => (n, outName)) ++
    byValMutDecls.map (fun (n, localName, _) => (n, localName))
  let rewrittenBody :=
    let b := applyNameSubstsStm mutRenames f.body
    let b := stripDecreaseArtifacts (expandReveals sfMap b)
    let b := normalizeBody isPureBooleBuiltinCallName b
    match b with | .Block stms => .Block (stripReturnAssumeFalse stms) | s => s
  -- `final(p)` reads (`MutRefFuture`) denote the post-state of a `&mut`
  -- parameter: rewrite them to the `_out` output first, then apply the name
  -- substitutions (which stop at `old(...)`, keeping pre-state reads on the
  -- input name).
  let mutFutureRenames := mutOutDecls.map (fun (n, outName, _) => (n, outName))
  let rewrittenEnsures := f.ensures.map (fun e =>
    applyNameSubstsExp mutRenames (substMutRefFutureOuts mutFutureRenames e))
  let hasRet := match f.returnType with | .Unit | .Empty => false | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let mutOutputDecls := mutOutDecls.map (fun (_, outName, payloadTy) => (outName, payloadTy))
  let inputNames := f.inputs.map Prod.fst
  let retNames := (if hasRet then [f.retName] else []) ++ mutOutputDecls.map Prod.fst
  let setVars := collectSetVars rewrittenBody
  let bodyHasForLoop := stmHasForLoop rewrittenBody
  let localsAll := collectProcedureLocals f.locals inputNames retNames setVars (hasForLoop := bodyHasForLoop)
  let localsAll := filterLocalsByUse (stripForLoopScaffoldingFromBody rewrittenBody) localsAll
  -- Drop names that the recovered for-loop's binder declares inline.
  let localsAll := filterOutForLoopBinders rewrittenBody localsAll
  -- Append shadow-locals for mutated by-value parameters.  These are
  -- referenced by the body (after the `<n>` → `<n>_local` rename above) but
  -- aren't surfaced by `collectSetVars` because the mutation appears as an
  -- `index_set` Call rather than an `Assign`.  Adding them ensures both the
  -- `var <n>_local : T;` declaration and the env entry needed to translate
  -- the body's references.
  let localsAll := localsAll ++ byValMutDecls.map (fun (_, localName, ty) =>
    { name := localName, ty := ty, origin := .implicitSet : LocalDeclInfo })
  -- Decide which `usize`/`isize` locals + for-loop binders are safe to
  -- retype as `Int` (used purely as sequence indices / length comparands /
  -- int arithmetic, never as bv operands or bv-typed call arguments).
  -- Then rewrite the body's `Assign.lhsTy` and the locals' types in one
  -- shot so the rest of the translator picks `expected = some Int`
  -- automatically; the for-loop arm reads the same set from BuildCtx.
  let promoted := IntPromotion.inferIntPromotableLocals localsAll rewrittenBody
  -- Read off signedness before the rewrite replaces the source types.
  let promotedUnsigned := IntPromotion.unsignedPromotedLocals promoted localsAll
  let localsAll := IntPromotion.rewriteLocalsForPromoted promoted localsAll
  let rewrittenBody := IntPromotion.rewriteBodyForPromoted promoted rewrittenBody
  let outputs := retDecls ++ mutOutputDecls
  let (inputBindings, inputNamesSan) ← mkMonoInputs f.inputs
  let (outputDecls?, outputNamesSan) ← mkMonoOutputs outputs
  let outputsAnn := ann outputDecls?
  let isDeclOnly := match f.body with | .Block [] => true | _ => false
  let envLocal := extendEnv env (f.inputs ++ outputs ++ localBindings localsAll)
  let (specElts, body, decrAnn) ← withPromotedLocals promoted promotedUnsigned <| withScope do
    addBoundVars inputNamesSan
    addBoundVars outputNamesSan
    let userSpecElts ← mkSpecElts envLocal f.requires rewrittenEnsures []
    -- A `[T; N]` return carries `ensures length(result) == N` to callers;
    -- the body proves it from the result's own length facts (a literal's
    -- length, a loop invariant, or a callee's ensures).  Scoped to the main
    -- return, not `&mut [T; N]` outputs: an output mutated inside a loop via
    -- a call (e.g. `compress` calling `compress_u32(&mut state, …)`) has no
    -- synthesized length invariant — loop detection only sees plain-assign /
    -- index_set mutations — so the ensures would be unprovable.
    let arrayRetElts ← fixedArrayLenElts mkLenEns retDecls
    -- Each `[T; N]` parameter also gets `ensures Sequence.length(p) == N`:
    -- spec-clause definedness cannot see the body's entry `assume`, so a user
    -- ensures reading the param needs the fact as a preceding clause.  An
    -- `ensures`, not a `requires`, so call sites stay obligation-free (exec
    -- callers may pass slice elements that carry no length fact); the callee
    -- proves it from the entry `assume`, and callers learn it for their
    -- argument.
    let arrayParamEnsElts ← fixedArrayLenElts mkLenEns f.inputs
    -- Wrapper/tuple length facts for params and outputs, including mut-outs:
    -- a caller that reassigns a local from a mut-out recovers its length from
    -- the ensures (e.g. `Y := conditional_negate_field_element(Y, …)`).  A
    -- body that loop-havocs a wrapper mut-out cannot prove that ensures
    -- without a synthesized loop invariant — same follow-up as the
    -- direct-array mut-out case above.  Synthesized facts go before the user
    -- spec so its clauses' definedness checks can use them.
    let specElts := (← wrapperLenSpecElts f.inputs outputs)
      ++ arrayParamEnsElts ++ arrayRetElts ++ userSpecElts
    -- Lower the source-level `decreases` clause BEFORE body translation so
    -- the bound-var stack is in a known-clean state.  Body translation may
    -- leave additional bound vars on the stack, which would produce
    -- dangling `bvar!N` indices in the decreases expression.
    let decrAnn ← decreasesToMeasureAnn envLocal f.decreases
    let (specElts, body) ←
      if isDeclOnly && isVecFromElemExecName f.name then
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
        -- (SynthConfig.fixedArrayLengths) Fixed-size-array params carry a
        -- compile-time length (`[T; N]`) lost when the type lowers to
        -- `Sequence T`.  Re-establish it at entry as `assume length(p) == N` —
        -- a *type* invariant (always true), modeled as an assume rather than a
        -- `requires` so it emits no call-site obligation and does not cascade an
        -- element-length proof onto callers: exec call sites include unsized
        -- slice elements (`compress` passing `&blocks[k]`) and call-mutated
        -- arrays after loop havoc, neither of which carries a length fact.
        -- (Proof-fn params carry a `requires` instead —
        -- `fixedArrayParamReqElts` — their specs reference length-preconditioned
        -- spec fns, and lemma call sites hold the threaded boundary facts.)
        -- Read-only arrays keep the fact across loops (loops
        -- havoc only modified vars); mut-out / by-value copies inherit it
        -- through their `copy := param` init below; arrays *mutated inside* a
        -- loop additionally get a loop invariant (in `tryForLoopRecovery`).
        let fixedArrayLenAssumes ← if (← getSynthConfig).fixedArrayLengths then
            f.inputs.filterMapM fun (name, ty) =>
              match arrayFixedLen? ty with
              | some n => do
                let pExpr ← resolveVar name
                pure (some (assumeStmt "" (Synth.fixedArrayLenFact pExpr n)))
              | none => pure none
          else pure ([] : List BStmt)
        -- Exec collections (`Vec<T>`, dynamically-sized slices) have `usize`
        -- lengths in Rust — a bound the unbounded `Sequence` lowering loses.
        -- Assumed at entry, never `requires`: the fact is a type invariant,
        -- true at every call site, so it must not mint caller obligations.
        -- Bodies rely on it to discharge the increment overflow guards Verus
        -- emits for index loops (`assert i + 1 <= usize::MAX`).  Spec `Seq<T>`
        -- is genuinely unbounded and deliberately does not match.
        let seqLenBoundAssumes ← if (← getSynthConfig).fixedArrayLengths then
            f.inputs.filterMapM fun (name, ty) =>
              if isUsizeLenSeqTyp ty then do
                let pExpr ← resolveVar name
                pure (some (assumeStmt "" (Synth.seqLenUsizeBoundFact pExpr)))
              else pure none
          else pure ([] : List BStmt)
        -- Init mutable-out variables from inputs
        let mutOutInits ← mutOutDecls.mapM (fun (inName, outName, payloadTy) => do
          let inExpr ← resolveVar inName
          let outTy ← typToBooleType payloadTy
          pure (setStmtTyped outTy (sanitizeVarName outName) inExpr))
        -- Init shadow locals for mutated by-value parameters from the
        -- corresponding input parameter.
        let byValInits ← byValMutDecls.mapM (fun (inName, localName, payloadTy) => do
          let inExpr ← resolveVar inName
          let localTy ← typToBooleType payloadTy
          pure (setStmtTyped localTy (sanitizeVarName localName) inExpr))
        let retVar? := if hasRet then some (f.retName, f.returnType) else none
        let bodyStmts ← stmToBoole envLocal projLayouts mutArgMap retVar? fnName rewrittenBody
        let allStmts := localStmts ++ fixedArrayLenAssumes ++ seqLenBoundAssumes ++ mutOutInits ++ byValInits ++ bodyStmts
        let body := BooleDDM.Block.block default (ann allStmts.toArray)
        pure (specElts, body)
    pure (specElts, body, decrAnn)
  let spec := ann (some (BooleDDM.Spec.spec_mk default (ann specElts)))
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn decrAnn spec (ann (some body)))

/-! ### Struct/Enum → BCmd -/

/-- Translate a struct to its Boole datatype (or, for a single-`[T; N]`-field
    wrapper, a transparent type synonym with identity ctor/dtor). -/
def structToBoole (s : Struct) : BuildM (Array BCmd) := do
  let dtName := datatypeNameOf s.name
  -- Wrapper-datatype trick: a single-field struct whose one field is a
  -- fixed-size array `[T; N]` is modeled as a *transparent* type synonym
  -- `<dt> := Sequence T` with an identity constructor and an identity
  -- destructor function, rather than an opaque datatype.  The opaque-datatype
  -- form needs a global length axiom `∀ s :: length(<dt>..<field>(s)) == N` to
  -- recover Verus's compile-time array length, but that axiom is unsound on a
  -- total constructor (it asserts every `Sequence T` has length `N`, e.g.
  -- `length(emptySeq) == 5`).  Here the length invariant rides on the ctor's
  -- `requires` instead, and an arbitrary `<dt>` is correctly *not* known to
  -- have length `N`.  Use sites are unchanged: the destructor is still named
  -- `<dt>..<field>` and the constructor `<dt>_ctor`.
  if let [(fname, fty)] := s.fields then
    if let some n := arrayFixedLen? fty then
      let ctorName := structCtorNameOf s.name
      let destructorName := datatypeDestructorNameOf s.name fname
      addFreeVars #[dtName, ctorName, destructorName]
      let elemBTy ← typToBooleType fty
      -- `command_typesynonym` takes type parameters as `Bindings`; the
      -- function commands take them as `TypeArgs` (`mkTypeArgsAnn`).
      let synTypeArgs : StrataDDM.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
        if s.typeParams.isEmpty then ann none
        else
          let bindings := s.typeParams.toArray.map fun param =>
            BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
          ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
      let fnTypeArgs := mkTypeArgsAnn s.typeParams
      -- `type <dt> := Sequence T;`
      let synCmd : BCmd :=
        .command_typesynonym default (ann dtName) synTypeArgs (ann none) elemBTy
      -- A single binding `<field> : Sequence T`, shared (by name) between the
      -- constructor and the destructor; the bodies are the identity `<field>`.
      let bindings := BooleDDM.Bindings.mkBindings default (ann #[
        BooleDDM.Binding.mkBinding default (ann (fieldAccessorNameOf fname))
          (BooleDDM.TypeP.expr elemBTy)])
      let identityBody := Bld.bvar 0
      -- `function <dt>_ctor (<field> : Sequence T) : <dt>
      --    requires Sequence.length(<field>) == N; { <field> }`
      let ctorReq : BooleDDM.SpecElt SourceRange :=
        .requires_spec default noLabel (ann none) (Synth.fixedArrayLenFact identityBody n)
      let ctorCmd : BCmd :=
        .command_fndef default (ann ctorName) fnTypeArgs bindings elemBTy
          (ann #[ctorReq]) identityBody (ann none)
      -- `function <dt>..<field> (<field> : Sequence T) : Sequence T { <field> }`
      let destructorCmd : BCmd :=
        .command_fndef default (ann destructorName) fnTypeArgs bindings elemBTy
          (ann #[]) identityBody (ann none)
      return #[synCmd, ctorCmd, destructorCmd]
  addFreeVars #[dtName]
  let ctorName := structCtorNameOf s.name
  let testerName := s!"{dtName}..is{ctorName}"
  let fieldNames := s.fields.map (fun (f, _) => fieldAccessorNameOf f)
  addFreeVars (#[ctorName, testerName] ++ fieldNames.toArray)
  let constrArgs ← if s.fields.isEmpty then
    pure (ann (none : Option (StrataDDM.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
  else do
    let bindings ← s.fields.toArray.mapM fun (fname, ty) => do
      let ty' ← typToBooleType ty
      pure (BooleDDM.Binding.mkBinding default (ann (fieldAccessorNameOf fname)) (BooleDDM.TypeP.expr ty'))
    pure (ann (some (ann bindings)))
  let constr := BooleDDM.Constructor.constructor_mk default (ann ctorName) constrArgs
  let constrList := BooleDDM.ConstructorList.constructorListAtom default constr
  let typeArgs : StrataDDM.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    if s.typeParams.isEmpty then ann none
    else
      let bindings := s.typeParams.toArray.map fun param =>
        BooleDDM.Binding.mkBinding default (ann (sanitizeIdent param)) (BooleDDM.TypeP.type default)
      ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
  let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann dtName) typeArgs constrList
  let dtCmd : BCmd := .command_datatypes default (ann #[dtDecl])
  -- Array-backed fields carry no global length axiom: the datatype is total,
  -- so `forall s : <dt> :: length(<dt>..<field>(s)) == N` is refuted by a
  -- constructor application of a wrong-length sequence.  Length facts ride on
  -- boundary requires/ensures instead, recursing through field selectors
  -- (`componentLenFacts`).
  pure #[dtCmd]

def enumToBoole (e : Enum) : BuildM BCmd := do
  let dtName := datatypeNameOf e.name
  addFreeVars #[dtName]
  if e.fields.isEmpty then
    if dtName == "Slice_Iter_iter" then
      requireSupport .tuple
      let args : StrataDDM.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
        ann (some (BooleDDM.Bindings.mkBindings default (ann #[
          BooleDDM.Binding.mkBinding default (ann "T") (BooleDDM.TypeP.type default)])))
      let tupleIdx ← resolveFreeVar tupleTypeName
      let rhs := fvarTy tupleIdx #[intTy, mapTy intTy (tvarTy "T")]
      pure (.command_typesynonym default (ann dtName) args (ann none) rhs)
    else
    -- Abstract type
      let args : StrataDDM.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
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
          pure (ann (none : Option (StrataDDM.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
        else do
          let bindings ← data.toArray.mapM fun (fname, ty) => do
            let ty' ← typToBooleType ty
            let fieldName := projFieldNameOf e.name variant fname
            pure (BooleDDM.Binding.mkBinding default (ann fieldName) (BooleDDM.TypeP.expr ty'))
          pure (ann (some (ann bindings)))
        pure (BooleDDM.Constructor.constructor_mk default (ann (enumCtorNameOf e.name variant)) constrArgs)
      | .tuple variant ts =>
        let constrArgs ← if ts.isEmpty then
          pure (ann (none : Option (StrataDDM.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)))
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
    let typeArgs : StrataDDM.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
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
  pure (.boole_procedure default name typeArgs inputBindings outputsAnn (ann none) spec (ann (some body)))

/-! ### Top-Level Declaration Translation -/

/-- Coalesce the `command_datatypes` commands in `cmds` into one mutual
    datatype block.  Strata's `command_datatypes` carries a newline-separated
    list of decls and elaborates them with two-phase name pre-registration, so
    decls sharing one command may reference one another.  Verus groups mutually
    recursive datatypes into a single `mutualBlock`; emitting each as its own
    command makes a sibling type "Undeclared" the moment a constructor field
    references it (no declaration order satisfies a cycle).  The merged command
    takes the slot of the first datatype command and the rest are dropped; every
    non-datatype command keeps its position, so per-datatype axioms still follow
    the (now-declared) types. -/
private def mergeDatatypeCommands (cmds : List BCmd) : List BCmd :=
  let dtDecls := cmds.foldl (init := (#[] : Array (BooleDDM.DatatypeDecl SourceRange)))
    fun acc c => match c with
      | .command_datatypes _ ⟨_, decls⟩ => acc ++ decls
      | _ => acc
  if dtDecls.size ≤ 1 then cmds
  else
    let merged : BCmd := .command_datatypes default (ann dtDecls)
    let out := cmds.foldl (init := ((#[] : Array BCmd), false)) fun st c =>
      match c with
      | .command_datatypes _ _ => if st.2 then st else (st.1.push merged, true)
      | _ => (st.1.push c, st.2)
    out.1.toList

/-- Literal exponents applied to `low_bits_mask` in an expression.  Feeds
    `lowBitsMaskValAxioms`; the cap only guards against an absurd `2^n`. -/
private partial def lowBitsMaskLitsInExp : Exp → List Nat
  | .Call fn _ args =>
    let here : List Nat :=
      match fn, args with
      | .Fun name, [arg] =>
        if isLowBitsMaskName name then
          match stripBoxWrappers arg with
          | .Const (.Int i) _ => if 0 ≤ i && i ≤ 512 then [i.toNat] else []
          | _ => []
        else []
      | _, _ => []
    here ++ args.flatMap lowBitsMaskLitsInExp
  | .CallLambda body args =>
    lowBitsMaskLitsInExp body ++ args.flatMap lowBitsMaskLitsInExp
  | .StructCtor _ fields => fields.flatMap (fun (_, e) => lowBitsMaskLitsInExp e)
  | .EnumCtor _ _ fields => fields.flatMap (fun (_, e) => lowBitsMaskLitsInExp e)
  | .TupleCtor _ data => data.flatMap lowBitsMaskLitsInExp
  | .Unary _ e => lowBitsMaskLitsInExp e
  | .Binary _ a b => lowBitsMaskLitsInExp a ++ lowBitsMaskLitsInExp b
  | .If c t f => lowBitsMaskLitsInExp c ++ lowBitsMaskLitsInExp t ++ lowBitsMaskLitsInExp f
  | .Bind bind body =>
    let bindLits := match bind with
      | .Let _ _ rhs => lowBitsMaskLitsInExp rhs
      | .Quant _ _ trigs => trigs.flatMap (·.flatMap lowBitsMaskLitsInExp)
      | .Lambda _ => []
      | .Choose _ pred => lowBitsMaskLitsInExp pred
    bindLits ++ lowBitsMaskLitsInExp body
  | .ArrayLiteral elems => elems.flatMap lowBitsMaskLitsInExp
  | .MatchBlock (scrut, _) body =>
    lowBitsMaskLitsInExp scrut ++ lowBitsMaskLitsInExp body
  | .Const _ _ | .Var _ => []

private partial def lowBitsMaskLitsInStm : Stm → List Nat
  | .Call _ _ args => args.flatMap lowBitsMaskLitsInExp
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => lowBitsMaskLitsInExp e
  | .AssertBitVector reqs enss =>
    reqs.flatMap lowBitsMaskLitsInExp ++ enss.flatMap lowBitsMaskLitsInExp
  | .AssertQuery _ body => lowBitsMaskLitsInStm body
  | .Assign _ _ rhs _ => lowBitsMaskLitsInExp rhs
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => lowBitsMaskLitsInStm s
  | .Return e? => (e?.map lowBitsMaskLitsInExp).getD []
  | .BreakOrContinue _ _ | .Reveal .. => []
  | .If cond b1 b2 =>
    lowBitsMaskLitsInExp cond ++ lowBitsMaskLitsInStm b1
      ++ (b2.map lowBitsMaskLitsInStm).getD []
  | .Loop _ _ cond body invs decrease =>
    let condLits := match cond with
      | some (s, e) => lowBitsMaskLitsInStm s ++ lowBitsMaskLitsInExp e
      | none => []
    condLits ++ lowBitsMaskLitsInStm body
      ++ invs.flatMap (fun inv => lowBitsMaskLitsInExp inv.body)
      ++ decrease.flatMap lowBitsMaskLitsInExp
  | .Block stms => stms.flatMap lowBitsMaskLitsInStm

private partial def lowBitsMaskLitsInDecl : Decl → List Nat
  | .assertion _ => []
  | .specFn f =>
    (f.body.map lowBitsMaskLitsInExp).getD []
      ++ f.recommends.flatMap lowBitsMaskLitsInExp
      ++ (f.decreases.map lowBitsMaskLitsInStm).getD []
  | .proofFn f =>
    f.requires.flatMap lowBitsMaskLitsInExp ++ f.ensures.flatMap lowBitsMaskLitsInExp
      ++ (f.body.map lowBitsMaskLitsInStm).getD []
      ++ f.decreases.flatMap lowBitsMaskLitsInStm
  | .execFn f =>
    f.requires.flatMap lowBitsMaskLitsInExp ++ f.ensures.flatMap lowBitsMaskLitsInExp
      ++ lowBitsMaskLitsInStm f.body ++ f.decreases.flatMap lowBitsMaskLitsInStm
  | .func f =>
    f.reqs.flatMap lowBitsMaskLitsInExp ++ f.postCondition.flatMap lowBitsMaskLitsInExp
  | .struct _ | .enum _ => []
  | .mutualBlock ds => ds.flatMap lowBitsMaskLitsInDecl

/-- The `<fn>_ret_len` axiom for a monomorphic `[T; N]`-returning spec fn:
    `∀ params :: <param length facts> → Sequence.length(<fn>(params)) == N`.
    A function has no named return for an `ensures`, so the length rides on an
    axiom, emitted right after the fn (axiom scope is positional).  `none` for
    polymorphic or non-array returns, and for fns nothing applies
    (`refNames`) — an inert axiom would only add solver noise. -/
private def specFnRetLenAxiom? (f : SpecFn) (refNames : Std.HashSet String) :
    BuildM (Option BCmd) := do
  let some n := arrayFixedLen? f.returnType | return none
  unless (fnTypeParams f.inputs f.returnType).isEmpty
      && refNames.contains (identToBoole f.name) do return none
  let fnName := identToBoole f.name
  let fnIdx ← resolveFreeVar fnName
  let k := f.inputs.length
  let app := if k == 0 then Bld.fvar fnIdx
    else Bld.appN (Bld.fvar fnIdx) ((List.range k).map (fun i => Bld.bvar (k - 1 - i)))
  let lenFact := Synth.fixedArrayLenFact app n
  -- Guard with the params' own length facts: the fn is total in the
  -- encoding, so the axiom must hold at every argument, and a body that
  -- returns a (modified) copy of its input has result length equal to the
  -- input's — unguarded, the axiom would contradict that defining equation
  -- off-domain, making the axiom set unsatisfiable.
  let hyps ← f.inputs.zipIdx.foldlM (fun acc ((_, ty), i) => do
    let facts ← componentLenFacts ty (Bld.bvar (k - 1 - i))
    pure (acc ++ facts)) []
  let body := match hyps with
    | [] => lenFact
    | h :: hs => Bld.boolImplies (hs.foldl Bld.boolAnd h) lenFact
  let axiomExpr ← if k == 0 then pure body else do
    let binders ← f.inputs.toArray.mapM (fun (x, ty) => do
      pure (sanitizeVarName x, ← typToBooleType ty))
    pure (forallExpr binders body)
  return some (.command_axiom default (someLabel s!"{fnName}_ret_len") axiomExpr)

/-- Ground value axioms for `low_bits_mask`, one per literal exponent the
    program applies it to:
      axiom [low_bits_mask_<n>_val]: nat.toInt(low_bits_mask(nat.fromInt(n))) == 2^n - 1
    — vstd's `pow2(n) - 1` at that instance; the fn itself stays
    uninterpreted (vstd bodies are not imported).  Emitted right after the
    fn's own decl, so the positional axiom scope covers every use site.
    `[]` for any other decl. -/
private def lowBitsMaskValAxioms (f : SpecFn) (allDecls : List Decl) :
    BuildM (List BCmd) := do
  unless isLowBitsMaskName f.name do return []
  let lits : List Nat := ((allDecls.flatMap lowBitsMaskLitsInDecl).eraseDups).mergeSort Nat.ble
  let fnIdx ← resolveFreeVar lowBitsMaskBooleName
  let toIntIdx ← resolveFreeVar "nat.toInt"
  let fromIntIdx ← resolveFreeVar "nat.fromInt"
  lits.mapM fun (n : Nat) => do
    let app := Bld.app (Bld.fvar fnIdx) (Bld.app (Bld.fvar fromIntIdx) (Bld.intConst (Int.ofNat n)))
    let axiomExpr := Bld.eq (Bld.app (Bld.fvar toIntIdx) app)
      (Bld.intConst (Int.ofNat (2 ^ n - 1)))
    pure (.command_axiom default (someLabel s!"low_bits_mask_{n}_val") axiomExpr)

partial def declToBoole (env : VarEnv) (projLayouts : List ProjLayout)
    (mutArgMap : MutArgMap) (sfMap : SpecFnMap)
    (allDecls : List Decl) (refNames : Std.HashSet String) :
    Decl → BuildM (List BCmd)
  | .assertion _ => return []
  | .specFn f => do
    let cmds ← specFnToBoole env (!f.isOpaque) f
    -- Synthesized length/value axioms attached to the fn's declaration.
    if !(← getSynthConfig).fixedArrayLengths then return cmds
    let retLenAxiom ← specFnRetLenAxiom? f refNames
    let lbmAxioms ← lowBitsMaskValAxioms f allDecls
    return cmds ++ retLenAxiom.toList ++ lbmAxioms
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
    let cmds ← structToBoole s
    return cmds.toList
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
        -- Every fn here is emitted as a `rec function`, so mark a datatype
        -- `decreases` parameter `@[cases]` (self-guarded: `structuralCasesParamIdx?`
        -- yields `none` for absent or int-valued measures).
        let casesIdx? := structuralCasesParamIdx? f
        let (inputBindings, inputNames) ← mkMonoInputs f.inputs casesIdx?
        let outputTy ← typToBooleType f.returnType
        let envLocal := extendEnv env f.inputs
        let (body, specElts, decrAnn) ← withScope do
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
          -- Fixed-array/wrapper length `requires` then `recommends`, both
          -- shared with `specFnToBoole`.
          let elts ← specFnParamLenElts f.inputs elts
          let elts ← specFnRecommendsElts envLocal f elts
          -- Thread the source `decreases` measure into the mutual-rec
          -- slot, mirroring `specFnToBoole`.  Previously hardcoded to
          -- `none`, so Strata's int-valued termination checker had no
          -- measure for mutually-recursive spec fns and rejected them
          -- with "requires a 'decreases' clause or a '@[cases]'".
          let decrAnn ←
            -- `@[cases]` supplies the structural measure; drop the datatype
            -- `decreases` rather than emit it into the int-valued slot.
            if casesIdx?.isSome then pure (Bld.mkMeasure none)
            else match f.decreases with
              | some (.Block stmts) => decreasesToMeasureAnn envLocal stmts
              | some s => decreasesToMeasureAnn envLocal [s]
              | none => pure (Bld.mkMeasure none)
          pure (body, elts, decrAnn)
        pure (BooleDDM.RecFnDecl.recfn_decl default name typeArgs inputBindings outputTy
          (ann specElts) decrAnn body)
      pure [BooleDDM.Command.command_recfndefs default (ann recDecls)]
    -- Translate non-spec declarations normally
    let otherCmds ← others.foldlM (fun acc d => do
      let cmds ← declToBoole env projLayouts mutArgMap sfMap allDecls refNames d
      return acc ++ cmds) []
    -- Mutually-recursive datatypes share one `mutualBlock`; merge their
    -- per-datatype commands so Strata sees a single mutual datatype block.
    return recCmds ++ mergeDatatypeCommands otherCmds

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

/-- Pair each abstract trait-method declaration whose return type is an
    associated-type projection (`<Self as Trait>::Assoc`, parsed as a
    `Typ.Struct` the program never declares as a type) with its concrete
    `TraitMethodImpl`, mapping the projection's Boole type name to the impl's
    resolved return type — e.g. `Ops_Arith_mul_Output` → `montgomeryPoint`.
    `typToBooleType` consults the result so the projection lowers to the
    concrete impl type rather than an undeclared nominal type.

    Single impl per trait method is assumed (true for the operator traits these
    benchmarks use): with several impls the last-seen return type wins, so a
    genuinely polymorphic associated type would need a per-instantiation
    encoding instead. -/
private def buildAssocTypeResolution (decls : List Decl) : Std.HashMap String Typ := Id.run do
  let returnTyp? : Decl → Option Typ
    | .specFn f => some f.returnType
    | .execFn f => some f.returnType
    | _ => none
  let implMethod? : Decl → Option Ident
    | .specFn f => f.traitImplMethod?
    | .execFn f => f.traitImplMethod?
    | _ => none
  -- Names the program declares as types: a projection carrier never appears
  -- here, so this guards against rewriting a real (generic) datatype that a
  -- trait method happens to return.
  let declaredTypeNames : List String := decls.filterMap fun d =>
    match d with
    | .struct s => some (datatypeNameOf s.name)
    | .enum e => some (datatypeNameOf e.name)
    | _ => none
  -- Index decls by name so an impl can find the abstract method it implements.
  let mut byName : Std.HashMap Ident Typ := {}
  for d in decls do
    match returnTyp? d with
    | some rt => byName := byName.insert (Decl.name d) rt
    | none => pure ()
  let mut resolution : Std.HashMap String Typ := {}
  for d in decls do
    match implMethod? d, returnTyp? d with
    | some method, some implRet =>
      match byName.get? method with
      | some (.Struct projName _) =>
        let booleName := datatypeNameOf projName
        if !declaredTypeNames.contains booleName && !isVecTypeName projName then
          resolution := resolution.insert booleName implRet
      | _ => pure ()
    | _, _ => pure ()
  return resolution

/-- Map each single-field `[T; N]` wrapper struct to its Boole type name →
    `(destructor name, N)` — e.g. `Scalar([u8; 32])` ⇒ `scalar ↦ ("scalar..bytes", 32)`,
    matching the wrapper-synonym branch of `structToBoole`.  Lets parameter/return
    length contracts be stated on the destructor (`length(scalar..bytes(x))==32`). -/
private def buildWrapperInfo (decls : List Decl) : Std.HashMap String (String × Nat) := Id.run do
  let mut m : Std.HashMap String (String × Nat) := {}
  for d in decls do
    match d with
    | .struct s =>
      match s.fields with
      | [(fname, fty)] =>
        match arrayFixedLen? fty with
        | some n =>
          m := m.insert (datatypeNameOf s.name) (datatypeDestructorNameOf s.name fname, n)
        | none => pure ()
      | _ => pure ()
    | _ => pure ()
  return m

/-- Fields of each monomorphic single-constructor struct, keyed by Boole
    datatype name (`BuildCtx.structFieldInfo`).  Wrapper structs are excluded
    (covered by `wrapperInfo`); `mutualBlock` members are included. -/
private partial def buildStructFieldInfo (decls : List Decl) :
    Std.HashMap String (List (String × Typ)) :=
  decls.foldl (init := {}) fun m d =>
    match d with
    | .struct s =>
      let isWrapper := match s.fields with
        | [(_, fty)] => (arrayFixedLen? fty).isSome
        | _ => false
      if s.typeParams.isEmpty && !isWrapper && !s.fields.isEmpty then
        m.insert (datatypeNameOf s.name) s.fields
      else m
    | .mutualBlock ds => (buildStructFieldInfo ds).fold (init := m) (·.insert · ·)
    | _ => m

/-- Variant payloads of each enum, keyed by Boole datatype name
    (`BuildCtx.enumFieldInfo`).  Field keys match `projFieldNameOf`: labeled
    fields keep their name, tuple fields use their position. -/
private partial def buildEnumFieldInfo (decls : List Decl) :
    Std.HashMap String (List String × List (String × List (String × Typ))) :=
  decls.foldl (init := {}) fun m d =>
    match d with
    | .enum e =>
      let variants := e.fields.map fun
        | .labeled vname data => (vname, data)
        | .tuple vname ts => (vname, ts.zipIdx.map (fun (t, i) => (toString i, t)))
      m.insert (datatypeNameOf e.name) (e.typeParams, variants)
    | .mutualBlock ds => (buildEnumFieldInfo ds).fold (init := m) (·.insert · ·)
    | _ => m

def declsToBooleProgram (decls : List Decl) :
    BuildM (Array BCmd) := do
  -- Resolve spec-level trait calls to the concrete impl that implements
  -- them before anything reads references: the impls' own spec fns become
  -- referenced and stay, the abstract generic trait fns become unreferenced
  -- and drop.
  let decls := TraitResolve.resolveTraitSpecCalls decls
  -- Resolve trait associated-type projections to their concrete impl types
  -- before any decl is lowered.  Built from the full decl set, since pruning
  -- below may drop the impl decls the resolution reads from.
  modify fun c => { c with assocTypeResolution := buildAssocTypeResolution decls }
  -- Wrapper-struct length info, stated on the destructor so the contract matches
  -- how bodies index the wrapper (see `wrapperLenSpecElts`).
  modify fun c => { c with wrapperInfo := buildWrapperInfo decls }
  -- Struct field and enum variant layouts, so length facts recurse through
  -- datatype selector paths (`componentLenFacts`).
  modify fun c => { c with structFieldInfo := buildStructFieldInfo decls }
  modify fun c => { c with enumFieldInfo := buildEnumFieldInfo decls }
  -- `vec2seq` branch: Verus emits stub `proc Vec_*` / `proc Slice_into_vec`
  -- wrappers (and a few other Vec-named procedures) to cover the Rust Vec
  -- surface — `Vec_new`, `Vec_len`, `Vec_push`, `Vec_from_elem`,
  -- `Slice_into_vec`, etc. Since we translate every Vec operation directly
  -- to the corresponding `Sequence.*` op at the call site (see the
  -- `isVecLenSpecName` / `isVecIndexSpecName` / `isViewName` handlers
  -- in `expToBoole`), those stub declarations are never invoked. Their
  -- specs are now redundant with the direct `Sequence.*` lowering and can
  -- leave dead symbols behind. Drop them here so the
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
        || n == "Num_wrapping_add"
        || n == "Slice_len"
        || n == "Slice_slice_index_get"
    | none => false
  -- Opaque type declarations for external types the translator always erases
  -- are dead: a `Vec` lowers to `Sequence` (never `Vec_vec`), and the `Global`
  -- allocator is a verification phantom that no emitted type names. Drop them so
  -- the output carries no unreferenced `type Vec_vec` / `type Alloc_global`.
  let isErasedOpaqueTypeDecl (d : Decl) : Bool :=
    match d with
    | .struct s => s.fields.isEmpty && (isVecTypeName s.name || isAllocatorTypeName s.name)
    | .enum e => e.fields.isEmpty && (isVecTypeName e.name || isAllocatorTypeName e.name)
    | _ => false
  -- Drop the inlined-at-callsite stubs *before* the reference-based prunes
  -- below.  Otherwise their (about-to-be-dropped) `ensures` clauses pin
  -- vstd spec fns that nothing else references — e.g. `Slice_len`'s
  -- ensures references `Slice_spec_slice_len`, keeping it alive after
  -- `pruneUnreferencedVstdSpecs` even though every real call to
  -- `slice.len()` lowers directly to `Sequence.length(slice)`.
  let decls := decls.filter (fun d => !isVec2SeqDroppedDecl d && !isErasedOpaqueTypeDecl d)
  -- Drop Verus-synthesised impl-block accessor spec fns that aren't
  -- transitively referenced by any user-level decl. Eager emission of every
  -- `Impl__N_arrow_*` bloats the output and slows verification; most tests
  -- use only a handful.
  let decls := pruneUnreferencedImpls decls
  -- Drop dead abstract trait-method decls before the vstd prune: a generic
  -- vstd spec fn named only by a dropped trait decl must not count as
  -- referenced, or it survives as an orphaned polymorphic declaration.
  let decls := pruneUnreferencedTraitMethodDecls decls
  let decls := pruneUnreferencedVstdSpecs decls
  let noParamFns := collectNoParamFnNamesFromDecls decls
  let projLayouts := buildProjLayouts decls
  let mutArgMap := collectMutArgMapFromDecls decls
  let sfMap := collectSpecFns decls
  let env := buildEnv decls noParamFns sfMap
  -- Detect whether any for-loop will be recovered
  let hasForLoop := declsHaveForLoop decls
  -- When for-loop recovery is active, skip translating iterator scaffolding declarations
  let filteredDecls := decls.filter fun d =>
    let name := declPrimaryName d
    !(hasForLoop && isForLoopScaffoldingDecl name)
  -- Callee names across all decls, computed once; gates the `<fn>_ret_len`
  -- axioms (`specFnRetLenAxiom?`).
  let refNames : Std.HashSet String := Std.HashSet.ofList (decls.flatMap Pruning.declRefs)
  -- Translate user declarations first to discover which support names are needed
  let mut userCmds : Array BCmd := #[]
  for d in filteredDecls do
    let cmds ← declToBoole env projLayouts mutArgMap sfMap decls refNames d
    userCmds := userCmds ++ cmds.toArray
  -- Support declarations are emitted from explicit requirements recorded
  -- during lowering, not from incidental free-variable references.
  let ctx ← get
  let supportNeeds := ctx.supportNeeds
  let supportCmds ← supportDeclCommands typToBooleType supportNeeds
  -- Closure-dependent helpers synthesized during expression lowering
  -- (e.g. the `Seq::map` int-recursion replacement). Spliced after the
  -- support decls so they precede the user decls that reference them.
  return supportCmds ++ ctx.synthDecls ++ userCmds

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
def translateDeclsWithPrelude (decls : List Decl) (preludeNames : Array String)
    (synthConfig : SynthConfig := {}) :
    Except String (Array BCmd × BuildCtx) :=
  let initCtx := { emptyCtx.addGlobalFreeVars preludeNames with synthConfig }
  match (declsToBooleProgram decls).run initCtx with
  | .ok (cmds, ctx) => .ok (cmds, ctx)
  | .error e => .error e

/-- Extract the declared name from a BooleDDM command, if it has one. -/
def cmdDeclName? : BCmd → Option String
  | .command_fndecl _ name _ _ _ => some name.val
  | .command_fndef _ name _ _ _ _ _ _ => some name.val
  | .command_choosefndef _ name _ _ _ _ _ => some name.val
  | .command_recfndefs _ _ => none  -- multiple names
  | .command_typedecl _ name _ => some name.val
  | .command_typesynonym _ name _ _ _ => some name.val
  | .command_datatypes _ decls =>
    -- `structToBoole`/`enumToBoole` emit one datatype per command, so a
    -- singleton names the command (letting shard dedupe drop re-declarations);
    -- multi-decl commands stay anonymous.
    match decls.val with
    | #[.datatype_decl _ name _ _] => some name.val
    | _ => none
  | .boole_procedure _ name _ _ _ _ _ _ => some name.val
  | .command_procedure _ name _ _ _ _ => some name.val
  | .command_cfg_procedure _ name _ _ _ _ => some name.val
  | .command_axiom _ label _ =>
    -- Labeled axioms are keyed as `axiom:<label>`: shard dedupe drops
    -- re-emitted copies, and the prefix keeps axiom keys from colliding with
    -- decl or prelude names.  Labels derive from the source construct, so
    -- equal labels carry equal formulas.  Unlabeled axioms stay anonymous.
    match label.val with
    | some (.label _ name) => some s!"axiom:{name.val}"
    | none => none
  | .command_var _ bind => some (match bind with | .bind_mk _ name _ _ => name.val)
  | .command_distinct _ _ _ => none
  | .command_constdecl _ name _ _ => some name.val
  | .command_block _ _ => none

end Translate

end VerusLean.Boole
