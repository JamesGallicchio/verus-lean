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

/-- For-loop ghost scaffolding lives in `VERUS_`-prefixed locals
    (`VERUS_ghost_iter`, `VERUS_old_snap`, `VERUS_old_iter`, …).  Any
    expression reading one is iterator bookkeeping: the recovered `for`
    drops the ghost state, so such references cannot lower and the
    surrounding clause/statement is scaffolding to drop. -/
partial def expRefsVERUSVar : Exp → Bool
  | .Const _ _ => false
  | .Var x => x.startsWith "VERUS_"
  | .Call _ _ args => args.any expRefsVERUSVar
  | .CallLambda body args => expRefsVERUSVar body || args.any expRefsVERUSVar
  | .StructCtor _ fields => fields.any (fun (_, e) => expRefsVERUSVar e)
  | .EnumCtor _ _ data => data.any (fun (_, e) => expRefsVERUSVar e)
  | .TupleCtor _ data => data.any expRefsVERUSVar
  | .Unary _ e => expRefsVERUSVar e
  | .Binary _ e1 e2 => expRefsVERUSVar e1 || expRefsVERUSVar e2
  | .If c t f => expRefsVERUSVar c || expRefsVERUSVar t || expRefsVERUSVar f
  | .Bind (.Let _ _ e) body => expRefsVERUSVar e || expRefsVERUSVar body
  | .Bind (.Quant _ _ trigs) body =>
    trigs.any (fun g => g.any expRefsVERUSVar) || expRefsVERUSVar body
  | .Bind (.Lambda _) body => expRefsVERUSVar body
  | .Bind (.Choose _ pred) body => expRefsVERUSVar pred || expRefsVERUSVar body
  | .ArrayLiteral elems => elems.any expRefsVERUSVar
  | .MatchBlock (scrut, _) body => expRefsVERUSVar scrut || expRefsVERUSVar body

/-- Statement-level view of `expRefsVERUSVar` (reads only; an assignment
    *to* a `VERUS_` local is judged by its name, not by this predicate). -/
def stmReadsVERUSVar : Stm → Bool
  | .Assign _ _ rhs _ => expRefsVERUSVar rhs
  | .Call _ _ args => args.any expRefsVERUSVar
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expRefsVERUSVar e
  | .AssertBitVector reqs enss => reqs.any expRefsVERUSVar || enss.any expRefsVERUSVar
  | .Return e? => e?.map expRefsVERUSVar |>.getD false
  | .If cond _ _ => expRefsVERUSVar cond
  | _ => false

private partial def isOptionIsSomeCheck : Exp → Bool
  | .Unary (.IsVariant dt "Some") _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  -- The iterator exit test carries a trivial guard conjunct
  -- (`isSome(...) && true`) and may sit under box coercions.
  | .Binary .And c (.Const (.Bool true) _) => isOptionIsSomeCheck c
  | .Unary (.Box _) e => isOptionIsSomeCheck e
  | .Unary (.Unbox _) e => isOptionIsSomeCheck e
  | _ => false

private partial def isOptionSomeProj : Exp → Bool
  | .Unary (.Proj dt "Some" "0" _ _) _ =>
    let s := dt.toString.toLower
    s.endsWith "option" || s.contains "option"
  -- The projection may sit under box coercions or a pass-through let
  -- binding whose body just returns the bound variable (`let t := Some_0(…) in t`).
  | .Unary (.Box _) e | .Unary (.Unbox _) e | .Unary .Trigger e => isOptionSomeProj e
  | .Bind (.Let v _ rhs) (.Var v') => v == v' && isOptionSomeProj rhs
  | .Bind (.Let v _ rhs) (.Unary (.Unbox _) (.Var v')) => v == v' && isOptionSomeProj rhs
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

  expVarRefsLocal : Exp → List String
    | .Const _ _ => []
    | .Var x => [x]
    | .Call _ _ args => (args.flatMap expVarRefsLocal).eraseDups
    | .CallLambda body args => (expVarRefsLocal body ++ (args.flatMap expVarRefsLocal)).eraseDups
    | .StructCtor _ fields => (fields.flatMap (fun (_, e) => expVarRefsLocal e)).eraseDups
    | .EnumCtor _ _ data => (data.flatMap (fun (_, e) => expVarRefsLocal e)).eraseDups
    | .TupleCtor _ data => (data.flatMap expVarRefsLocal).eraseDups
    | .Unary _ e => expVarRefsLocal e
    | .Binary _ e1 e2 => (expVarRefsLocal e1 ++ expVarRefsLocal e2).eraseDups
    | .If c t f => (expVarRefsLocal c ++ expVarRefsLocal t ++ expVarRefsLocal f).eraseDups
    | .Bind (.Let _ _ e) body => (expVarRefsLocal e ++ expVarRefsLocal body).eraseDups
    | .Bind (.Quant _ _ trigs) body =>
      ((trigs.flatMap (fun g => g.flatMap expVarRefsLocal)) ++ expVarRefsLocal body).eraseDups
    | .Bind (.Lambda _) body => expVarRefsLocal body
    | .Bind (.Choose _ pred) body =>
      (expVarRefsLocal pred ++ expVarRefsLocal body).eraseDups
    | .ArrayLiteral elems => (elems.flatMap expVarRefsLocal).eraseDups
    | .MatchBlock (scrut, _) body => (expVarRefsLocal scrut ++ expVarRefsLocal body).eraseDups

  stmtAssignedVarLocal? : Stm → Option String
    | .Assign lhs _ _ _ => lvalueVarName? lhs
    | _ => none

  stmtRefsLocal : Stm → List String
    | .Assign _ _ rhs _ => expVarRefsLocal rhs
    | .Call _ _ args => (args.flatMap expVarRefsLocal).eraseDups
    | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expVarRefsLocal e
    | .AssertBitVector reqs enss => ((reqs.flatMap expVarRefsLocal) ++ (enss.flatMap expVarRefsLocal)).eraseDups
    | .Return e? => e?.map expVarRefsLocal |>.getD []
    | .If cond _ _ => expVarRefsLocal cond
    | _ => []

  filterScaffoldingStms (stms : List Stm) : List Stm :=
    let directKeep : Stm → Bool
      | .Assign lhs _ _ _ =>
        match lvalueVarName? lhs with
        | some name =>
          -- `VERUS_*` and decrease locals are loop-scaffolding.  Ordinary
          -- `tmp%N` locals may carry user computations after normalization
          -- (array reads, rotate calls, wrapping adds, etc.), so keep them
          -- when a later retained statement references them.
          !(name.startsWith "VERUS_" || name.startsWith "decrease" ||
            name.startsWith "tmp%%")
        | none => true
      | .Call fn _ _ =>
        !(isIteratorNextName fn || isIntoIterName fn || isGhostPervasiveCallName fn)
      | .Assume (.Const (.Bool false) _) => false
      | _ => true
    let rec go (needed : List String) (keptRev : List Stm) : List Stm → List Stm
      | [] => keptRev
      | s :: rest =>
        let assigned? := stmtAssignedVarLocal? s
        let keep := directKeep s ||
          (assigned?.map (fun name => needed.contains name) |>.getD false)
        if keep then
          let needed' :=
            let needed' := assigned?.map (fun name => needed.erase name) |>.getD needed
            ((stmtRefsLocal s) ++ needed').eraseDups
          go needed' (s :: keptRev) rest
        else
          go needed keptRev rest
    -- Forward taint pass first: a statement reading `VERUS_*` ghost state
    -- (or a local computed from it) is iterator bookkeeping the recovered
    -- loop cannot lower, and the names it assigns are tainted in turn
    -- (`tmp5 := Std_specs_Iter_trigger_peek_implications(…); assert tmp5`).
    let taintFiltered :=
      let step := fun (acc : List Stm × List String) (s : Stm) =>
        let (keptRev, tainted) := acc
        let readsTainted := (stmtRefsLocal s).any (fun n =>
          n.startsWith "VERUS_" || tainted.contains n)
        if readsTainted then
          match stmtAssignedVarLocal? s with
          | some n => (keptRev, n :: tainted)
          | none => (keptRev, tainted)
        else (s :: keptRev, tainted)
      (stms.foldl step ([], [])).1.reverse
    go [] [] taintFiltered.reverse

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
    -- Rewrite first: a *user* invariant arrives as
    -- `let i := (if isSome(peek …ghost…) then Some_0(…) else arbitrary()) in P`
    -- and the rewrite replaces the ghost-peek binding with the recovered loop
    -- binder, eliminating the ghost references.  What still mentions the
    -- ghost-iterator API or `VERUS_*` state after rewriting is synthesized
    -- iterator bookkeeping the recovered loop drops.
    let rewritten := rewriteForLoopInvariant loopVar inv.body
    if isGhostIteratorInvariant inv.body || expRefsVERUSVar rewritten then none
    else
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
  | .Bind (.Choose _ pred) body =>
    (expVarRefs pred ++ expVarRefs body).eraseDups
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
  -- Forward taint pass first: iterator-setup statements read the `VERUS_*`
  -- ghost state the recovered loop drops (`Std_specs_Iter_new(VERUS_iter,…)`)
  -- — they cannot lower regardless of callee name, and locals computed from
  -- them are scaffolding in turn.
  let taintFiltered :=
    let step := fun (acc : List Stm × List String) (s : Stm) =>
      let (keptRev, tainted) := acc
      let readsTainted := (stmtRefs s).any (fun n =>
        n.startsWith "VERUS_" || tainted.contains n)
      if readsTainted then
        match stmtAssignedVar? s with
        | some n => (keptRev, n :: tainted)
        | none => (keptRev, tainted)
      else (s :: keptRev, tainted)
    (stms.foldl step ([], [])).1.reverse
  go [] [] taintFiltered.reverse

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
