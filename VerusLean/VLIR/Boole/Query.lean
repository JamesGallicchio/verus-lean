/-
  Boole.Query — VLIR `AssertQuery` scaffolding inspection.

  Verus `assert(...) by { ... }` blocks lower to a stylised VLIR shape:
  a leading run of `assume` statements (the user requires), then the
  proof body, then a trailing run of `assert`/`assertLean` statements
  (the obligations that get echoed back as the surrounding `assume`).
  The translator needs a few small predicates to (a) recognise that
  shape, (b) split it into reqs/ens lists, and (c) detect the
  surrounding `assert e; assume e;` echo pair so the assume can be
  elided after lowering.

  Pure inspection over `Stm` / `Exp` — no `BuildM`, no BooleDDM
  emission. Lives next to `Normalize.lean` rather than `Translate.lean`
  because the predicates here are about VLIR shape, not translation.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Normalize

namespace VerusLean.Boole.Query

open VerusLean
open VerusLean.Boole.Normalize

def sameExpShape (e1 e2 : Exp) : Bool := e1 == e2

def queryBodyStms : Stm → List Stm
  | .Block [s] => queryBodyStms s
  | .Block stms => stms
  | s => [s]

def takeLeadingAssumes : List Stm → List Exp × List Stm
  | (.Assume e) :: rest =>
    let (reqs, tail) := takeLeadingAssumes rest
    (e :: reqs, tail)
  | stms => ([], stms)

def takeLeadingEnsuresRev : List Stm → List Exp × List Stm
  | (.Assert e) :: rest | (.AssertLean e) :: rest =>
    let (ens, tail) := takeLeadingEnsuresRev rest
    (e :: ens, tail)
  | stms => ([], stms)

def queryReqEnsFromBody (body : Stm) : Option (List Exp × List Exp) :=
  let stms := (queryBodyStms body).map stripSingletonBlocks
  let (reqs, rest) := takeLeadingAssumes stms
  let (ensRev, _) := takeLeadingEnsuresRev rest.reverse
  let ens := ensRev.reverse
  if ens.isEmpty then none else some (reqs, ens)

def isQueryScaffoldingAssume (assumed : Exp) : Stm → Bool
  | .AssertBitVector _ ensures => ensures.any (fun e => sameExpShape e assumed)
  | .AssertQuery _ body =>
    match queryReqEnsFromBody body with
    | some (_, ensures) => ensures.any (fun e => sameExpShape e assumed)
    | none => false
  | _ => false

def isQueryStmt : Stm → Bool
  | .AssertBitVector _ _ => true
  | .AssertQuery _ _ => true
  | _ => false

def isTrivialTrueAssert : Stm → Bool
  | .Assert (.Const (.Bool true) _) => true
  | .AssertLean (.Const (.Bool true) _) => true
  | _ => false

def isAssertAssumeEcho (a : Stm) (assumed : Exp) : Bool :=
  match a with
  | .Assert e => sameExpShape e assumed
  | .AssertLean e => sameExpShape e assumed
  | _ => false

def assertQueryModeLabel : AssertQueryMode → String
  | .NonLinear => "nonlinear_query"
  | .BitVector => "bitvector_query"
  | .Other _ => "assert_query"

end VerusLean.Boole.Query
