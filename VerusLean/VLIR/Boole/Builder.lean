/-
  Boole.Builder — Uniform combinators for constructing BooleDDM AST nodes.

  This module provides a small uniform API that internally routes to
  the appropriate BooleDDM constructor.  The translator speaks in terms of
  these combinators so that:

    1.  The translator's regular call-site style is preserved.
    2.  If BooleDDM's surface API evolves, only this file changes.
    3.  SourceRange metadata is defaulted to `default` in one place.
-/
import StrataBoole.Boole
import Strata.Languages.Core.DDMTransform.ASTtoCST

namespace VerusLean.Boole.Builder

open Strata
open Strata.BooleDDM
open StrataDDM (SourceRange)

/-! ## Type abbreviations -/

abbrev BExpr := BooleDDM.Expr SourceRange
abbrev BType := BooleDDM.BooleType SourceRange
abbrev BStmt := BooleDDM.Statement SourceRange
abbrev BCmd  := BooleDDM.Command SourceRange
abbrev BBlock := BooleDDM.Block SourceRange

private def ann (v : α) : StrataDDM.Ann α SourceRange := ⟨default, v⟩

/-! ## Type constructors -/

def boolTy : BType := .bool default
def intTy  : BType := .int default
def strTy  : BType := .string default

def bvTy (w : Nat) : BType :=
  match w with
  | 1  => .bv1 default
  | 8  => .bv8 default
  | 16 => .bv16 default
  | 32 => .bv32 default
  | 64 => .bv64 default
  | 128 => .bv128 default
  | _  => panic! s!"bvTy: unsupported bitvector width {w} (expected 1|8|16|32|64|128); \
    callers must filter via Coercions.isSupportedBvWidth"

def mapTy (key val : BType) : BType := .Map default key val
def seqTy (elem : BType) : BType := .Sequence default elem
def arrowTy (dom cod : BType) : BType := .arrow default dom cod
def tvarTy (name : String) : BType := .tvar default name

def fvarTy (idx : Nat) (args : Array BType := #[]) : BType :=
  .fvar default idx args

def unknownTy : BType := tvarTy "$__unknown_type"

/-! ## Expression constructors — leaves -/

def fvar (idx : Nat) : BExpr := .fvar default idx
def bvar (idx : Nat) : BExpr := .bvar default idx

/-- Strata's native `as_uint(e)` cast — unsigned bv→int.  Lowers to
    `Bv<W>.ToUInt` at Core, which cvc5 understands as nonneg-by-construction
    via the SMT-LIB `bv2nat` family. -/
def castToInt (sourceTy : BType) (e : BExpr) : BExpr :=
  .as_uint default sourceTy e

/-- Strata's native `as_sint(e)` cast — signed bv→int. -/
def castToSInt (sourceTy : BType) (e : BExpr) : BExpr :=
  .as_sint default sourceTy e

/-- Narrowing int→bv cast `as_bv<w>(e)` (Core `Int.ToBv<w>` → SMT `int_to_bv`).
    Per-width tokens (1/8/16/32/64/128); `none` for any other width so callers
    fall back to the uninterpreted support-decl cast. -/
def castToBv (w : Nat) (e : BExpr) : Option BExpr :=
  match w with
  | 1   => some (.as_bv1   default e)
  | 8   => some (.as_bv8   default e)
  | 16  => some (.as_bv16  default e)
  | 32  => some (.as_bv32  default e)
  | 64  => some (.as_bv64  default e)
  | 128 => some (.as_bv128 default e)
  | _   => none

def boolConst (b : Bool) : BExpr :=
  if b then .btrue default else .bfalse default

def intConst (n : Int) : BExpr :=
  if n >= 0 then
    .natToInt default ⟨default, n.toNat⟩
  else
    .neg_expr default intTy (.natToInt default ⟨default, n.natAbs⟩)

def bitvecConstNat (w : Nat) (n : Nat) : BExpr :=
  match w with
  | 1  => .bv1Lit default ⟨default, n⟩
  | 8  => .bv8Lit default ⟨default, n⟩
  | 16 => .bv16Lit default ⟨default, n⟩
  | 32 => .bv32Lit default ⟨default, n⟩
  | 64 => .bv64Lit default ⟨default, n⟩
  | 128 => .bv128Lit default ⟨default, n⟩
  | _  => panic! s!"bitvecConstNat: unsupported bitvector width {w} (expected 1|8|16|32|64|128)"

def bitvecConst (w : Nat) (bv : BitVec w) : BExpr :=
  bitvecConstNat w bv.toNat

/-! ## Expression constructors — compound -/

def ite (c t e : BExpr) : BExpr := .if default unknownTy c t e
def iteTyped (ty : BType) (c t e : BExpr) : BExpr := .if default ty c t e

def eq (a b : BExpr) : BExpr := .equal default unknownTy a b
def neq (a b : BExpr) : BExpr := .not_equal default unknownTy a b
def eqTyped (ty : BType) (a b : BExpr) : BExpr := .equal default ty a b
def neqTyped (ty : BType) (a b : BExpr) : BExpr := .not_equal default ty a b

/-- Curried function application: `app fn arg`. -/
def app (fn arg : BExpr) : BExpr := .app default fn arg

/-- Multi-argument function application: `appN fn [a, b, c]` = `fn(a)(b)(c)`. -/
def appN (fn : BExpr) (args : List BExpr) : BExpr :=
  args.foldl (fun acc arg => .app default acc arg) fn

/-- Boolean operations. -/
def boolNot (e : BExpr) : BExpr := .not default e
def boolAnd (a b : BExpr) : BExpr := .and default a b
def boolOr (a b : BExpr) : BExpr := .or default a b
def boolImplies (a b : BExpr) : BExpr := .implies default a b
def boolEquiv (a b : BExpr) : BExpr := .equiv default a b

/-- Integer arithmetic. -/
def intAdd (a b : BExpr) : BExpr := .add_expr default intTy a b
def intSub (a b : BExpr) : BExpr := .sub_expr default intTy a b
def intMul (a b : BExpr) : BExpr := .mul_expr default intTy a b
def intDiv (a b : BExpr) : BExpr := .div_expr default intTy a b
def intMod (a b : BExpr) : BExpr := .mod_expr default intTy a b
def intNeg (e : BExpr)   : BExpr := .neg_expr default intTy e

/-- Integer comparisons. -/
def intLe (a b : BExpr) : BExpr := .le default intTy a b
def intLt (a b : BExpr) : BExpr := .lt default intTy a b
def intGe (a b : BExpr) : BExpr := .ge default intTy a b
def intGt (a b : BExpr) : BExpr := .gt default intTy a b

/-- Bitvector arithmetic. -/
def bvAdd (w : Nat) (a b : BExpr) : BExpr := .add_expr default (bvTy w) a b
def bvSub (w : Nat) (a b : BExpr) : BExpr := .sub_expr default (bvTy w) a b
def bvMul (w : Nat) (a b : BExpr) : BExpr := .mul_expr default (bvTy w) a b
def bvUDiv (w : Nat) (a b : BExpr) : BExpr := .div_expr default (bvTy w) a b
def bvUMod (w : Nat) (a b : BExpr) : BExpr := .mod_expr default (bvTy w) a b
def bvSDiv (w : Nat) (a b : BExpr) : BExpr := .bvsdiv default (bvTy w) a b
def bvSMod (w : Nat) (a b : BExpr) : BExpr := .bvsmod default (bvTy w) a b
def bvNeg (w : Nat) (e : BExpr) : BExpr := .neg_expr default (bvTy w) e

/-- Bitvector bitwise operations. -/
def bvAnd (w : Nat) (a b : BExpr) : BExpr := .bvand default (bvTy w) a b
def bvOr  (w : Nat) (a b : BExpr) : BExpr := .bvor default (bvTy w) a b
def bvXor (w : Nat) (a b : BExpr) : BExpr := .bvxor default (bvTy w) a b
def bvNot (w : Nat) (e : BExpr)   : BExpr := .bvnot default (bvTy w) e
def bvShl (w : Nat) (a b : BExpr) : BExpr := .bvshl default (bvTy w) a b
def bvUShr (w : Nat) (a b : BExpr) : BExpr := .bvushr default (bvTy w) a b

/-- Bitvector unsigned comparisons. -/
def bvUle (w : Nat) (a b : BExpr) : BExpr := .le default (bvTy w) a b
def bvUlt (w : Nat) (a b : BExpr) : BExpr := .lt default (bvTy w) a b
def bvUge (w : Nat) (a b : BExpr) : BExpr := .ge default (bvTy w) a b
def bvUgt (w : Nat) (a b : BExpr) : BExpr := .gt default (bvTy w) a b

/-- Bitvector signed comparisons. -/
def bvSle (w : Nat) (a b : BExpr) : BExpr := .bvsle default (bvTy w) a b
def bvSlt (w : Nat) (a b : BExpr) : BExpr := .bvslt default (bvTy w) a b
def bvSge (w : Nat) (a b : BExpr) : BExpr := .bvsge default (bvTy w) a b
def bvSgt (w : Nat) (a b : BExpr) : BExpr := .bvsgt default (bvTy w) a b

/-- Map operations. -/
def mapGet (m k : BExpr) : BExpr := .map_get default unknownTy unknownTy m k
def mapSet (m k v : BExpr) : BExpr := .map_set default unknownTy unknownTy m k v

/-- Sequence length. -/
def seqLength (s : BExpr) : BExpr := .seq_length default unknownTy s
def seqSelect (s i : BExpr) : BExpr := .seq_select default unknownTy s i
def seqUpdate (s i v : BExpr) : BExpr := .seq_update default unknownTy s i v

/-- Empty sequence carrying an explicit element type: `Sequence.empty<T>()`.
    The Core `seq_empty` production embeds the element type in the surface
    syntax, so element types without a dedicated typed constant (type
    parameters, structs, …) round-trip through this polymorphic form. -/
def seqEmpty (elemTy : BType) : BExpr := .seq_empty default elemTy

/-- Old expression (procedure pre-state). -/
def old (e : BExpr) : BExpr := .old default unknownTy e
def oldTyped (ty : BType) (e : BExpr) : BExpr := .old default ty e

/-! ## Quantifiers -/

private def bindsToDeclList (bs : Array (String × BType)) : BooleDDM.DeclList SourceRange :=
  if bs.isEmpty then
    let bind := Bind.bind_mk default (ann "") (ann none) unknownTy
    .declAtom default bind
  else
    let mkBind (name : String) (ty : BType) :=
      Bind.bind_mk default (ann name) (ann none) ty
    let first := bs[0]!
    let init := DeclList.declAtom default (mkBind first.1 first.2)
    bs[1:].foldl (fun acc (name, ty) =>
      DeclList.declPush default acc (mkBind name ty))
      init

def forallExpr (binds : Array (String × BType)) (body : BExpr) : BExpr :=
  if binds.isEmpty then body else .forall_unicode default (bindsToDeclList binds) body

def existsExpr (binds : Array (String × BType)) (body : BExpr) : BExpr :=
  if binds.isEmpty then body else .exists_unicode default (bindsToDeclList binds) body

private def exprsToTriggerGroup (es : Array BExpr) : BooleDDM.TriggerGroup SourceRange :=
  .trigger default (ann es)

private def groupsToTriggers (groups : Array (Array BExpr)) : BooleDDM.Triggers SourceRange :=
  let first := exprsToTriggerGroup groups[0]!
  groups[1:].foldl (fun acc g => .triggersPush default acc (exprsToTriggerGroup g))
    (.triggersAtom default first)

/-- An empty group (e.g. from `#![trigger]` with no expressions) would lower
    to an illegal `:pattern ()`; drop those before deciding whether any real
    trigger exists. -/
private def nonEmptyTriggerGroups (groups : Array (Array BExpr)) : Array (Array BExpr) :=
  groups.filter (fun g => !g.isEmpty)

/-- Strata's `triggersPush` pretty-printer (Core/DDMTransform/Grammar.lean)
    concatenates its two sub-terms with no separator, so printing 2+ trigger
    groups back out as Boole source text produces unparseable syntax (seen on
    `verus/examples/quantifiers.rs`'s multi-`#![trigger ...]` case). Until that
    upstream Strata bug is fixed, cap trigger emission to a single group; the
    common single-group case (e.g. `#![trigger v[k]]`) is unaffected. -/
private def usableTriggerGroups (groups : Array (Array BExpr)) : Array (Array BExpr) :=
  let nonEmpty := nonEmptyTriggerGroups groups
  if nonEmpty.size > 1 then #[] else nonEmpty

/-- Like `forallExpr`, but attaches trigger groups when present. Non-triggered quantifiers
    are unaffected. -/
def forallExprT (binds : Array (String × BType)) (triggerGroups : Array (Array BExpr))
    (body : BExpr) : BExpr :=
  if binds.isEmpty then body
  else
    let groups := usableTriggerGroups triggerGroups
    if groups.isEmpty then .forall_unicode default (bindsToDeclList binds) body
    else .forall_unicodeT default (bindsToDeclList binds) (groupsToTriggers groups) body

/-- See `forallExprT`. -/
def existsExprT (binds : Array (String × BType)) (triggerGroups : Array (Array BExpr))
    (body : BExpr) : BExpr :=
  if binds.isEmpty then body
  else
    let groups := usableTriggerGroups triggerGroups
    if groups.isEmpty then .exists_unicode default (bindsToDeclList binds) body
    else .exists_unicodeT default (bindsToDeclList binds) (groupsToTriggers groups) body

/-- Build `fun x : T, ... => body` using Strata Core's `lambda` op.

    The body's return type slot is filled with `unknownTy`; Strata's
    elaborator infers the concrete return type from `body`. With zero
    binders the lambda would be vacuous, so we just return the body. -/
def lambdaExpr (binds : Array (String × BType)) (body : BExpr) : BExpr :=
  if binds.isEmpty then body
  else .lambda default unknownTy (bindsToDeclList binds) body

/-! ## Statement constructors -/

private def mkLabel (label : String) : StrataDDM.Ann (Option (BooleDDM.Label SourceRange)) SourceRange :=
  if label.isEmpty || label == "||" then
    ann none
  else
    ann (some (.label default (ann label)))

def varStmt (name : String) (ty : BType) : BStmt :=
  let bind := Bind.bind_mk default (ann name) (ann none) ty
  let decls := DeclList.declAtom default bind
  .varStatement default decls

def initStmt (name : String) (ty : BType) (rhs : BExpr) : BStmt :=
  .initStatement default ty (ann name) rhs

def setStmtTyped (ty : BType) (name : String) (rhs : BExpr) : BStmt :=
  let lhs := BooleDDM.Lhs.lhsIdent default (ann name)
  .assign default ty lhs rhs

def setStmt (name : String) (rhs : BExpr) : BStmt :=
  setStmtTyped unknownTy name rhs

def havocStmt (name : String) : BStmt :=
  .havoc_statement default (ann name)

/-- Build `lhs := choose v : T :: pred;`.  Strata lowers this to
    `havoc lhs; assume pred[v ↦ lhs];` in the verify pipeline (see
    `StrataBoole/Verify.lean`'s `.choose_assign` arm).  The
    `pred` expression must be translated with `v` bound at de Bruijn 0
    so the parser/elaborator picks it up correctly. -/
def chooseAssignStmt (lhs : String) (v : String) (vTy : BType) (pred : BExpr) : BStmt :=
  let bind := MonoBind.mono_bind_mk default (ann v) vTy
  .choose_assign default (ann lhs) bind pred

def assertStmt (label : String) (e : BExpr) : BStmt :=
  .assert default (ann none) (mkLabel label) e

def assumeStmt (label : String) (e : BExpr) : BStmt :=
  .assume default (mkLabel label) e

def coverStmt (label : String) (e : BExpr) : BStmt :=
  .cover default (ann none) (mkLabel label) e

def callStmt (lhs : Array String) (pname : String) (args : Array BExpr) : BStmt :=
  if lhs.isEmpty then
    .call_statement default (ann pname) (ann (args.map (.callArgExpr default ·)))
  else
    .boole_call_statement default (ann (lhs.map ann)) (ann pname) (ann args)

def blockStmt (label : String) (body : Array BStmt) : BStmt :=
  .block_statement default (ann label) (.block default (ann body))

def iteStmt (cond : BExpr) (thenBody : Array BStmt) (elseBody : Array BStmt) : BStmt :=
  let thenBlock := BooleDDM.Block.block default (ann thenBody)
  let elseNode :=
    if elseBody.isEmpty then
      BooleDDM.Else.else0 default
    else
      .else1 default (.block default (ann elseBody))
  .if_statement default (.condDet default cond) thenBlock elseNode

private def invsFromArray (invs : Array BExpr) : BooleDDM.Invariants SourceRange :=
  invs.foldl (fun acc e =>
    BooleDDM.Invariants.consInvariants default (ann none) e acc)
    (.nilInvariants default)

def mkMeasure (m : Option BExpr) : StrataDDM.Ann (Option (BooleDDM.Measure SourceRange)) SourceRange :=
  match m with
  | none => ann none
  | some m => ann (some (.measure_mk default m))

def whileStmt (guard : BExpr) (measure : Option BExpr)
    (invs : Array BExpr) (body : Array BStmt) : BStmt :=
  .while_statement default (.condDet default guard) (mkMeasure measure)
    (invsFromArray invs) (.block default (ann body))

def forToStmt (loopVar : String) (loopTy : BType)
    (start limit : BExpr) (measure : Option BExpr)
    (invs : Array BExpr) (body : Array BStmt) : BStmt :=
  let binder := MonoBind.mono_bind_mk default (ann loopVar) loopTy
  -- Field order in `for_to_by_statement` is (v, init, limit, step?, decr?,
  -- invs, body).  `step?` is `none` because the verus-lean translator only
  -- emits +1 ranges; `decr?` carries the optional measure.
  .for_to_by_statement default binder start limit (ann none)
    (mkMeasure measure) (invsFromArray invs) (.block default (ann body))

-- Strata removed unlabeled `exit` (upstream `dc7a029ae`: ambiguous as
-- break vs. continue, "never used").  Only labeled exits exist now; the
-- sole caller (`.BreakOrContinue`) already rejects the unlabeled case.
def exitStmt (label : String) : BStmt :=
  .exit_statement default (ann label)

/-- Early return: emit `exit <procName>;`. Strata's procedure translation
    wraps the body in a labeled block named after the procedure, so exiting
    the block named `procName` exits the procedure. Callers that want to
    "return e" should set the output variable first, then call this. -/
def returnStmt (procName : String) : BStmt :=
  .exit_statement default (ann procName)

end VerusLean.Boole.Builder
