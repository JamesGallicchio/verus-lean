/-
  Boole.ForLoop — heuristic recovery of source `for` loops from VLIR.

  Verus lowers `for` loops through iterator scaffolding before serialization.
  This module recognizes that VLIR shape and returns a source-oriented loop
  plan.  BooleDDM emission stays in `Translate.lean`.
-/

import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names
import VerusLean.VLIR.Boole.Normalize

namespace VerusLean.Boole.ForLoop

open VerusLean
open VerusLean.Boole.Names
open VerusLean.Boole.Normalize

def shouldDropAssignAsForLoopScaffolding (lhs : LValue) : Bool :=
  match lvalueVarName? lhs with
  | some name => name.startsWith "VERUS_ghost_" || name == "VERUS_loop_result"
  | none => false

def shouldDropForLoopScaffoldingLocal (name : String) : Bool :=
  name.startsWith "VERUS_" || name.startsWith "decrease"

def isForLoopScaffoldingVar (name : String) : Bool :=
  name.startsWith "VERUS_" || name.startsWith "tmp" || name.startsWith "decrease"

private def isOptionIsSomeCheck : Exp → Bool
  | .Unary (.IsVariant dt "Some") _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  | _ => false

private def isOptionSomeProj : Exp → Bool
  | .Unary (.Proj dt "Some" "0" _ _) _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  | _ => false

private partial def flattenBody : Stm → List Stm
  | .Block stms => stms.flatMap flattenBody
  | s => [s]

structure ForLoopBodyInfo where
  loopVarName : String
  loopVarTy : Typ
  userBody : List Stm
deriving Repr

private partial def matchForLoopBody? (body : Stm) : Option ForLoopBodyInfo := do
  let stms := flattenBody body
  let (ifStm, postIfStms) ← findOptionIf stms
  let (cond, thenBranch, elseBranch) ← match ifStm with
    | .If c b1 b2 => some (c, b1, b2)
    | _ => none
  guard (isOptionIsSomeCheck cond)
  guard (hasBreak elseBranch)
  let thenStms := flattenBody thenBranch
  match extractLoopVarFromThen thenStms with
  | some (loopVarName, loopVarTy, userBodyInThen) =>
    let userBody := userBodyInThen ++ filterScaffoldingStms postIfStms
    some { loopVarName, loopVarTy, userBody }
  | none =>
    match findLoopVarAfterIf postIfStms with
    | some (loopVarName, loopVarTy, userBody) =>
      some { loopVarName, loopVarTy, userBody }
    | none => none
where
  findOptionIf (stms : List Stm) : Option (Stm × List Stm) :=
    let rec go (rest : List Stm) : Option (Stm × List Stm) :=
      match rest with
      | [] => none
      | s :: tail =>
        match s with
        | .If cond _ _ =>
          if isOptionIsSomeCheck cond then some (s, tail)
          else go tail
        | .Block inner =>
          match go (flattenBody (.Block inner)) with
          | some (ifS, innerRest) => some (ifS, innerRest ++ tail)
          | none => go tail
        | _ => go tail
    go stms

  hasBreak : Option Stm → Bool
    | some (.BreakOrContinue _ true) => true
    | some (.Block stms) => stms.any fun
      | .BreakOrContinue _ true => true
      | _ => false
    | _ => false

  extractLoopVarFromThen (stms : List Stm) : Option (String × Typ × List Stm) :=
    match stms with
    | [] => none
    | s :: rest =>
      match s with
      | .Assign lhs ty rhs _ =>
        match lvalueVarName? lhs with
        | some name =>
          if isOptionSomeProj rhs && !isForLoopScaffoldingVar name then
            some (name, ty, filterScaffoldingStms rest)
          else
            extractLoopVarFromThen rest
        | none => extractLoopVarFromThen rest
      | _ => extractLoopVarFromThen rest

  findLoopVarAfterIf (stms : List Stm) : Option (String × Typ × List Stm) :=
    match stms with
    | [] => none
    | s :: rest =>
      match s with
      | .Assign lhs ty _rhs _ =>
        match lvalueVarName? lhs with
        | some name =>
          if !isForLoopScaffoldingVar name then
            some (name, ty, filterScaffoldingStms rest)
          else
            findLoopVarAfterIf rest
        | none => findLoopVarAfterIf rest
      | _ => findLoopVarAfterIf rest

  filterScaffoldingStms (stms : List Stm) : List Stm :=
    stms.filter fun
      | .Assign lhs _ _ _ =>
        match lvalueVarName? lhs with
        | some name => !isForLoopScaffoldingVar name
        | none => true
      | .Call fn _ _ =>
        !(isIteratorNextName fn || isIntoIterName fn || isGhostPervasiveCallName fn)
      | .Assume (.Const (.Bool false) _) => false
      | _ => true

structure ForLoopRangeInfo where
  startExp : Exp
  endExp : Exp
  iterVarName : Option String := none
deriving Repr

private partial def stripBoxUnbox : Exp → Exp
  | .Unary (.Box _) e => stripBoxUnbox e
  | .Unary (.Unbox _) e => stripBoxUnbox e
  | e => e

private partial def findRangeSetup? (preStms : List Stm) : Option ForLoopRangeInfo := do
  let subs := preStms.filterMap fun
    | .Assign lhs _ rhs _ =>
      match lvalueVarName? lhs with
      | some name => some (name, rhs)
      | none => none
    | _ => none
  let rangeInfo ← preStms.findSome? fun
    | .Assign _lhs _ (.StructCtor dt fields) _ =>
      if isRangeTypeName dt then
        match fields with
        | [("start", startE), ("end", endE)] =>
          some (stripBoxUnbox (substExps subs startE), stripBoxUnbox (substExps subs endE))
        | _ => none
      else none
    | _ => none
  some { startExp := rangeInfo.1, endExp := rangeInfo.2 }

private partial def isGhostIteratorPeekPattern : Exp → Bool
  | .If cond thenE _elseE =>
    isOptionIsSomeCheck cond && isOptionSomeProj thenE
  | _ => false

private partial def isGhostIteratorInvariant : Exp → Bool
  | .Unary (.Unbox _) e => isGhostIteratorInvariant e
  | .Unary (.Box _) e => isGhostIteratorInvariant e
  | .Call fn _ _ =>
    let s := (CallFun.name fn).toString.toLower
    s.contains "forloopghostiterator" || s.contains "ghost_invariant" ||
    s.contains "exec_invariant" || s.contains "ghost_ensures" ||
    s.contains "ghost_advance"
  | .Unary _ e => isGhostIteratorInvariant e
  | _ => false

private partial def rewriteForLoopInvariant (loopVar : String) : Exp → Exp
  | .Bind (.Let v _ty rhs) body =>
    if v == loopVar then
      let isGhostPeek := isGhostPeekRhs rhs
      if isGhostPeek then
        substExp v (.Var loopVar) body
      else .Bind (.Let v _ty (rewriteForLoopInvariant loopVar rhs)) (rewriteForLoopInvariant loopVar body)
    else
      let isGhostPeek := isGhostPeekRhs rhs
      if isGhostPeek then
        substExp v (.Var loopVar) (rewriteForLoopInvariant loopVar body)
      else
        .Bind (.Let v _ty (rewriteForLoopInvariant loopVar rhs)) (rewriteForLoopInvariant loopVar body)
  | .Unary (.Unbox _) e => rewriteForLoopInvariant loopVar e
  | .Unary (.Box _) e => rewriteForLoopInvariant loopVar e
  | e => e
where
  isGhostPeekRhs : Exp → Bool
    | .Bind (.Let _ _ innerRhs) innerBody =>
      hasGhostPeekCall innerRhs || isGhostIteratorPeekPattern innerBody || isGhostPeekRhs innerBody
    | .If cond thenE _elseE =>
      isOptionIsSomeCheck cond && isOptionSomeProj thenE
    | .Unary (.Unbox _) e | .Unary (.Box _) e => isGhostPeekRhs e
    | .Call fn _ _ =>
      let s := (CallFun.name fn).toString.toLower
      s.contains "ghost_peek" || s.contains "ghost_peek_next"
    | _ => false

  hasGhostPeekCall : Exp → Bool
    | .Call fn _ _ =>
      let s := (CallFun.name fn).toString.toLower
      s.contains "ghost_peek" || s.contains "ghost_peek_next"
    | .Unary _ e => hasGhostPeekCall e
    | _ => false

private def processForLoopInvariants (loopVar : String) (invs : List LoopInvariant)
    : List LoopInvariant :=
  invs.filterMap fun inv =>
    if isGhostIteratorInvariant inv.body then none
    else
      let rewritten := rewriteForLoopInvariant loopVar inv.body
      some { inv with body := rewritten }

private def processForLoopDecrease (loopVar : String) (decrease : List Exp) : List Exp :=
  decrease.map (rewriteForLoopInvariant loopVar)

private partial def flattenAllBlocks (stms : List Stm) : List Stm :=
  stms.flatMap fun
    | .Block inner => flattenAllBlocks inner
    | s => [s]

private partial def expVarRefs : Exp → List String
  | .Const _ _ => []
  | .Var x => [x]
  | .Call _ _ args => (args.flatMap expVarRefs).eraseDups
  | .CallLambda body args => (expVarRefs body ++ (args.flatMap expVarRefs)).eraseDups
  | .StructCtor _ fields => (fields.flatMap (fun (_, e) => expVarRefs e)).eraseDups
  | .EnumCtor _ _ data => (data.flatMap (fun (_, e) => expVarRefs e)).eraseDups
  | .TupleCtor _ data => (data.flatMap expVarRefs).eraseDups
  | .Unary _ e => expVarRefs e
  | .Binary _ e1 e2 => (expVarRefs e1 ++ expVarRefs e2).eraseDups
  | .If c t f => (expVarRefs c ++ expVarRefs t ++ expVarRefs f).eraseDups
  | .Bind (.Let _ _ e) body => (expVarRefs e ++ expVarRefs body).eraseDups
  | .Bind (.Quant _ _ trigs) body =>
    ((trigs.flatMap (fun g => g.flatMap expVarRefs)) ++ expVarRefs body).eraseDups
  | .Bind (.Lambda _) body => expVarRefs body
  | .ArrayLiteral elems => (elems.flatMap expVarRefs).eraseDups
  | .MatchBlock (scrut, _) body => (expVarRefs scrut ++ expVarRefs body).eraseDups

private def stmtAssignedVar? : Stm → Option String
  | .Assign lhs _ _ _ => lvalueVarName? lhs
  | _ => none

private def stmtRefs : Stm → List String
  | .Assign _ _ rhs _ => expVarRefs rhs
  | .Call _ _ args => (args.flatMap expVarRefs).eraseDups
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expVarRefs e
  | .AssertBitVector reqs enss => ((reqs.flatMap expVarRefs) ++ (enss.flatMap expVarRefs)).eraseDups
  | .Return e? => e?.map expVarRefs |>.getD []
  | .If cond _ _ => expVarRefs cond
  | _ => []

private def shouldKeepPreambleDirectly : Stm → Bool
  | .Assign lhs _ _ _ =>
    match lvalueVarName? lhs with
    | some name => !isForLoopScaffoldingVar name && !name.startsWith "decrease"
    | none => true
  | .Call fn _ _ =>
    !(isIteratorNextName fn || isIntoIterName fn || isGhostPervasiveCallName fn)
  | _ => true

private def filterForLoopPreamble (stms : List Stm) : List Stm :=
  let rec go (needed : List String) (keptRev : List Stm) : List Stm → List Stm
    -- We scan `stms.reverse`, so prepending each kept stmt rebuilds the
    -- retained prefix in source order already. Reversing again would flip
    -- the preamble and reorder effectful setup statements.
    | [] => keptRev
    | s :: rest =>
      let assigned? := stmtAssignedVar? s
      let keep := shouldKeepPreambleDirectly s ||
        (assigned?.map (fun name => needed.contains name) |>.getD false)
      if keep then
        let needed' :=
          let needed' := assigned?.map (fun name => needed.erase name) |>.getD needed
          ((stmtRefs s) ++ needed').eraseDups
        go needed' (s :: keptRev) rest
      else
        go needed keptRev rest
  go [] [] stms.reverse

structure RecoveredForLoop where
  preStms : List Stm
  loopVarName : String
  loopVarTy : Typ
  startExp : Exp
  endExp : Exp
  invariants : List LoopInvariant
  decrease : List Exp
  userBody : List Stm
  postStms : List Stm
deriving Repr

partial def recoverForLoop? (stms : List Stm) : Option RecoveredForLoop := do
  let (preStms, loopStm, postStms) ← findForLoop [] stms
  match loopStm with
  | .Loop true _label _cond body invs decrease =>
    let info ← matchForLoopBody? body
    let allPreStms := flattenAllBlocks preStms
    let rangeInfo ← findRangeSetup? allPreStms
    some {
      preStms := filterForLoopPreamble allPreStms
      loopVarName := info.loopVarName
      loopVarTy := info.loopVarTy
      startExp := rangeInfo.startExp
      endExp := rangeInfo.endExp
      invariants := processForLoopInvariants info.loopVarName invs
      decrease := processForLoopDecrease info.loopVarName decrease
      userBody := info.userBody
      postStms := postStms
    }
  | _ => none
where
  findForLoop (pre : List Stm) (rest : List Stm) :
      Option (List Stm × Stm × List Stm) :=
    match rest with
    | [] => none
    | s :: tail =>
      match s with
      | .Loop true _ _ _ _ _ => some (pre.reverse, s, tail)
      | .Block inner =>
        match findForLoop [] (flattenAllBlocks [.Block inner]) with
        | some (innerPre, loopStm, innerPost) =>
          some (pre.reverse ++ innerPre, loopStm, innerPost ++ tail)
        | none => findForLoop (s :: pre) tail
      | _ => findForLoop (s :: pre) tail

end VerusLean.Boole.ForLoop
