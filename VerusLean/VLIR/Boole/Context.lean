/-
  Boole.Context — translation-owned name/index context.

  BooleDDM stores variables as numeric free-variable and bound-variable
  indices.  VLIR stores source names.  This module owns that name-to-index
  mapping for the translator so it is not coupled to Strata's CST formatting
  context.
-/
import Std.Data.HashSet
import Strata.Languages.Boole.Boole

namespace VerusLean.Boole.Context

open Strata

structure BuildScope where
  boundVars : Array String := #[]
deriving Inhabited

inductive SupportDecl where
  | nat
  | natToInt
  | intToNat
  | bvToInt (w : Nat) (signed : Bool)
  | bvToNat (w : Nat) (signed : Bool)
  | intToBv (w : Nat) (signed : Bool)
  | bvWiden (fromW toW : Nat) (signed : Bool)
  /-- Polymorphic 2-ary tuple type (Verus represents all tuples as nested
      binary tuples; `Unit` is the 0-ary case). Emits a datatype
      `Tuple (T0, T1) { Tuple_ctor_2(Tuple_2_0 : T0, Tuple_2_1 : T1) }`,
      giving the verifier native constructor/accessor reasoning rather
      than uninterpreted stubs. -/
  | tuple
  /-- Abstract declaration for `Seq_lib_zip_with<A, B>(s: Sequence A, t:
      Sequence B): Sequence (Tuple A B)`. Emitted as a support decl
      (rather than in the Seq prelude text) because its return type
      references `Tuple`, which itself is only available after the
      `.tuple` support decl is emitted. -/
  | seqZipWith
  /-- Abstract fallback helper for Rust `[x; n]` values when no fixed
      compile-time length is available at the call site. Fixed `[x; N]`
      arrays lower to concrete `Sequence.build` chains instead. -/
  | arrayFill
  /-- Polymorphic abstract `Set (T)` type, plus the higher-order /
      Set-typed Seq builtins below.  These are emitted as support decls
      (not in the Seq prelude text) because they are *polymorphic and
      higher-order*: when present-but-unused, Strata's SMT encoder cannot
      monomorphize their free type vars (`Unimplemented encoding for type
      var`).  As support decls they are emitted only when a call site
      actually references them — where the type vars monomorphize — so an
      unused builtin never reaches the encoder.  (`Seq::map` is normally
      replaced by `emitSeqMapDecls` synthesis and so needs none of these.) -/
  | set
  | seqNew
  | seqLibMap
  | seqLibMapValues
  | seqLibFilter
  | seqLibSortBy
  | seqLibToSet
  | setFinite
  deriving DecidableEq, Repr

/-- Feature toggles for the translator's *synthesized* verification aids —
    invariants / axioms / preconditions that re-introduce facts Verus's types
    and iterators guarantee but the `Sequence` lowering drops.  All default
    `true` (current behavior); flipping one off only reduces *completeness*
    (some out-of-bounds obligations revert to `unknown`), never soundness, so
    it is a safe knob for measuring each aid's impact.  The fact *builders*
    live in `Boole.Synth`; these flags gate their *emission* at each site. -/
structure SynthConfig where
  /-- Fixed-size-array `Sequence.length(_) == N` facts: the struct-field
      length axiom, the per-parameter entry assume, and the
      mutated-in-loop length invariant. -/
  fixedArrayLengths : Bool := true
  /-- For-range loop lower-bound invariant `lo <= i` (Strata's `for` hands the
      body only the upper bound `i <= hi`, via the loop guard). -/
  loopLowerBound : Bool := true
  /-- Synthesized `Seq::map` recursion prefix-range precondition
      `0 <= n && n <= Sequence.length(s)`. -/
  seqMapPrecond : Bool := true
  deriving Repr

structure BuildCtx where
  allFreeVars : Array String := #[]
  supportNeeds : Array SupportDecl := #[]
  scopes : Array BuildScope := #[{}]
  /-- Counter for synthetic labels (e.g. `implicitLoopLabel`) that must
      be unique per-translation. Using a monotonic counter avoids the
      collision risk of deriving labels from AST structural hashes. -/
  loopLabelCounter : Nat := 0
  /-- Names of `usize` / `isize` locals (and for-loop binders) that the
      `IntPromotion` pass decided are safe to retype to `Int` for the
      currently-translated procedure.  Scoped around procedure lowering
      with `withPromotedLocals`.  Consulted by `tryForLoopRecovery` to
      decide whether to lower the binder type as `Int`. -/
  promotedLocals : Std.HashSet String := ∅
  /-- Top-level commands synthesized on demand during expression lowering
      (e.g. the first-order closure function + int-recursive helper that
      replace a `Seq::map` lambda — see `emitSeqMapDecls`). Spliced into
      the program after the support declarations in `declsToBooleProgram`.
      Unlike `SupportDecl`s these are closure-dependent, so they can't be
      a fixed enum. -/
  synthDecls : Array (BooleDDM.Command SourceRange) := #[]
  /-- Monotonic counter for naming synthesized declarations uniquely. -/
  synthFnCounter : Nat := 0
  /-- Feature toggles for synthesized verification aids; all-on by default
      (current behavior).  See `SynthConfig`. -/
  synthConfig : SynthConfig := {}

abbrev BuildM := StateT BuildCtx (Except String)

namespace BuildCtx

def empty : BuildCtx := {}

def pushScope (ctx : BuildCtx) : BuildCtx :=
  { ctx with scopes := ctx.scopes.push {} }

def popScope (ctx : BuildCtx) : BuildCtx :=
  if ctx.scopes.size <= 1 then
    ctx
  else
    { ctx with scopes := ctx.scopes.pop }

def addGlobalFreeVars (ctx : BuildCtx) (names : Array String) : BuildCtx :=
  names.foldl
    (fun acc name =>
      if acc.allFreeVars.any (· == name) then acc
      else { acc with allFreeVars := acc.allFreeVars.push name })
    ctx

def addSupportNeed (ctx : BuildCtx) (need : SupportDecl) : BuildCtx :=
  if ctx.supportNeeds.any (· == need) then ctx
  else { ctx with supportNeeds := ctx.supportNeeds.push need }

def freeVarIndex? (ctx : BuildCtx) (name : String) : Option Nat :=
  ctx.allFreeVars.findIdx? (· == name)

def pushBoundVar (ctx : BuildCtx) (name : String) : BuildCtx :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let scope := { scope with boundVars := scope.boundVars.push name }
  { ctx with scopes := ctx.scopes.set! idx scope }

def addBoundVars (ctx : BuildCtx) (names : Array String) : BuildCtx :=
  let idx := ctx.scopes.size - 1
  let scope := ctx.scopes[idx]!
  let scope := { scope with boundVars := scope.boundVars ++ names }
  { ctx with scopes := ctx.scopes.set! idx scope }

def allBoundVars (ctx : BuildCtx) : Array String :=
  ctx.scopes.foldl (fun acc scope => acc ++ scope.boundVars) #[]

end BuildCtx

def emptyCtx : BuildCtx := BuildCtx.empty

def requireSupport (need : SupportDecl) : BuildM Unit :=
  modify (·.addSupportNeed need)

/-- The active synthesized-aid toggles for this translation. -/
def getSynthConfig : BuildM SynthConfig := return (← get).synthConfig

/-- Return a fresh unique loop-label id (0, 1, 2, …) and increment the
    counter in `BuildCtx`. Callers typically format it as
    `sanitizeIdent s!"loop_{n}"`. -/
def freshLoopLabelId : BuildM Nat := do
  let ctx ← get
  let n := ctx.loopLabelCounter
  set { ctx with loopLabelCounter := n + 1 }
  pure n

/-- Return a fresh unique id for a synthesized declaration and increment
    the counter in `BuildCtx`. -/
def freshSynthId : BuildM Nat := do
  let ctx ← get
  let n := ctx.synthFnCounter
  set { ctx with synthFnCounter := n + 1 }
  pure n

/-- Record a synthesized top-level command for later splicing into the
    program (see `BuildCtx.synthDecls`). -/
def pushSynthDecl (cmd : BooleDDM.Command SourceRange) : BuildM Unit :=
  modify (fun ctx => { ctx with synthDecls := ctx.synthDecls.push cmd })

/-- Set the per-procedure promoted-locals set.  Private — callers use
    `withPromotedLocals` for proper save/restore semantics. -/
private def setPromotedLocals (promoted : Std.HashSet String) : BuildM Unit :=
  modify (fun ctx => { ctx with promotedLocals := promoted })

/-- Run an action with the given per-procedure promoted-locals set. -/
def withPromotedLocals (promoted : Std.HashSet String) (action : BuildM α) : BuildM α := do
  let old := (← get).promotedLocals
  setPromotedLocals promoted
  let result ← action
  modify (fun ctx => { ctx with promotedLocals := old })
  pure result

/-- True if `name` was promoted to `Int` for the currently-translated
    procedure. -/
def isPromotedLocal (name : String) : BuildM Bool := do
  let ctx ← get
  return ctx.promotedLocals.contains name

end VerusLean.Boole.Context
