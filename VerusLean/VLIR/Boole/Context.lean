/-
  Boole.Context — translation-owned name/index context.

  BooleDDM stores variables as numeric free-variable and bound-variable
  indices.  VLIR stores source names.  This module owns that name-to-index
  mapping for the translator so it is not coupled to Strata's CST formatting
  context.
-/
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
  deriving DecidableEq, Repr

structure BuildCtx where
  allFreeVars : Array String := #[]
  supportNeeds : Array SupportDecl := #[]
  scopes : Array BuildScope := #[{}]
  /-- Counter for synthetic labels (e.g. `implicitLoopLabel`) that must
      be unique per-translation. Using a monotonic counter avoids the
      collision risk of deriving labels from AST structural hashes. -/
  loopLabelCounter : Nat := 0

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

/-- Return a fresh unique loop-label id (0, 1, 2, …) and increment the
    counter in `BuildCtx`. Callers typically format it as
    `sanitizeIdent s!"loop_{n}"`. -/
def freshLoopLabelId : BuildM Nat := do
  let ctx ← get
  let n := ctx.loopLabelCounter
  set { ctx with loopLabelCounter := n + 1 }
  pure n

end VerusLean.Boole.Context
