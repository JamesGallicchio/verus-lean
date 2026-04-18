/-
  Boole.Normalize — source-level VLIR rewrites before BooleDDM lowering.

  These passes operate only on VLIR expressions/statements.  They intentionally
  do not allocate Boole fvars/bvars or inspect BooleDDM syntax.
-/

import VerusLean.VLIR.Defs

namespace VerusLean.Boole.Normalize

open VerusLean

def isFuelVar : Exp → Bool
  | .Var name => name.startsWith "fuel%" || name.startsWith "fuel_"
  | _ => false

def normalizeCallArgs (args : List Exp) : List Exp :=
  args.filter (fun e => !isFuelVar e)

/-! ## Expression and statement substitution -/

private partial def expVarRefs : Exp → List String :=
  let merge (xs : List (List String)) : List String := (xs.foldl (· ++ ·) []).eraseDups
  fun
  | .Const _ _ => []
  | .Var x => [x]
  | .Call _ _ args => merge (args.map expVarRefs)
  | .CallLambda body args => (expVarRefs body ++ merge (args.map expVarRefs)).eraseDups
  | .StructCtor _ fields => merge <| fields.map (fun (_, e) => expVarRefs e)
  | .EnumCtor _ _ data => merge <| data.map (fun (_, e) => expVarRefs e)
  | .TupleCtor _ data => merge (data.map expVarRefs)
  | .Unary _ e => expVarRefs e
  | .Binary _ e1 e2 => (expVarRefs e1 ++ expVarRefs e2).eraseDups
  | .If c t f => (expVarRefs c ++ expVarRefs t ++ expVarRefs f).eraseDups
  | .Bind (.Let _ _ e) body => (expVarRefs e ++ expVarRefs body).eraseDups
  | .Bind (.Quant _ _ trigs) body =>
    merge ((trigs.map (fun g => merge <| g.map expVarRefs)) ++ [expVarRefs body])
  | .Bind (.Lambda _) body => expVarRefs body
  | .ArrayLiteral elems => merge (elems.map expVarRefs)
  | .MatchBlock (scrut, _) body => (expVarRefs scrut ++ expVarRefs body).eraseDups

private def freshenedName (base : String) (used : List String) : String :=
  if !used.contains base then base
  else
    let rec go : List Nat → String
      | [] => s!"{base}_fresh"
      | i :: rest =>
        let cand := s!"{base}_{i}"
        if used.contains cand then go rest else cand
    go (List.range (used.length + 1))

private def triggerVarRefs (trigs : List (List Exp)) : List String :=
  let flatten (xs : List (List String)) : List String := (xs.foldl (· ++ ·) []).eraseDups
  flatten <| trigs.map (fun g => flatten <| g.map expVarRefs)

mutual
partial def substExp (name : String) (rhs : Exp) : Exp → Exp
  | .Const c ty => .Const c ty
  | .Var x => if x == name then rhs else .Var x
  | .Call fn typs exps => .Call fn typs (exps.map (substExp name rhs))
  | .CallLambda body args =>
    .CallLambda (substExp name rhs body) (args.map (substExp name rhs))
  | .StructCtor dt fields =>
    .StructCtor dt (fields.map fun (n, e) => (n, substExp name rhs e))
  | .EnumCtor dt variant data =>
    .EnumCtor dt variant (data.map fun (n, e) => (n, substExp name rhs e))
  | .TupleCtor size data =>
    .TupleCtor size (data.map (substExp name rhs))
  | .Unary .Old e => .Unary .Old e
  | .Unary op e => .Unary op (substExp name rhs e)
  | .Binary op e1 e2 => .Binary op (substExp name rhs e1) (substExp name rhs e2)
  | .If c t f => .If (substExp name rhs c) (substExp name rhs t) (substExp name rhs f)
  | .Bind bind body =>
    match bind with
    | .Let v ty e =>
      let e' := substExp name rhs e
      if v == name then .Bind (.Let v ty e') body
      else
        let rhsRefs := expVarRefs rhs
        if rhsRefs.contains v then
          let v' := freshenedName v (rhsRefs ++ expVarRefs body ++ [name])
          let bodyRenamed := substExp v (.Var v') body
          .Bind (.Let v' ty e') (substExp name rhs bodyRenamed)
        else
          .Bind (.Let v ty e') (substExp name rhs body)
    | .Quant q vars trigs =>
      if vars.any (fun (v, _) => v == name) then .Bind (.Quant q vars trigs) body
      else
        let rhsRefs := expVarRefs rhs
        let (vars', trigs', body') := renameBinderPack vars trigs body rhsRefs [name]
        let trigs'' := trigs'.map (fun g => g.map (substExp name rhs))
        .Bind (.Quant q vars' trigs'') (substExp name rhs body')
    | .Lambda vars =>
      if vars.any (fun (v, _) => v == name) then .Bind (.Lambda vars) body
      else
        let rhsRefs := expVarRefs rhs
        let (vars', _, body') := renameBinderPack vars [] body rhsRefs [name]
        .Bind (.Lambda vars') (substExp name rhs body')
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (substExp name rhs))
  | .MatchBlock scrut body =>
    let (e, t) := scrut
    .MatchBlock (substExp name rhs e, t) (substExp name rhs body)

private partial def renameBinderPack
    (vars : List (String × Typ))
    (trigs : List (List Exp))
    (body : Exp)
    (rhsRefs : List String)
    (avoid : List String) :
    (List (String × Typ) × List (List Exp) × Exp) :=
  let rec go
      (rest : List (String × Typ))
      (used : List String)
      (trigsAcc : List (List Exp))
      (bodyAcc : Exp)
      (revVars : List (String × Typ)) :
      (List (String × Typ) × List (List Exp) × Exp) :=
    match rest with
    | [] => (revVars.reverse, trigsAcc, bodyAcc)
    | (v, ty) :: tail =>
      if rhsRefs.contains v then
        let v' := freshenedName v used
        let renameExpr := substExp v (.Var v')
        let trigs' := trigsAcc.map (fun g => g.map renameExpr)
        let body' := renameExpr bodyAcc
        go tail (v' :: used) trigs' body' ((v', ty) :: revVars)
      else
        go tail (v :: used) trigsAcc bodyAcc ((v, ty) :: revVars)
  go vars
    (avoid ++ rhsRefs ++ vars.map Prod.fst ++ expVarRefs body ++ triggerVarRefs trigs)
    trigs body []
end

def substExps (subs : List (String × Exp)) (e : Exp) : Exp :=
  subs.foldl (fun acc (n, rhs) => substExp n rhs acc) e

partial def substStm (name : String) (rhs : Exp) : Stm → Stm
  | .Call fn typs args => .Call fn typs (args.map (substExp name rhs))
  | .Assert e => .Assert (substExp name rhs e)
  | .AssertBitVector reqs ens =>
    .AssertBitVector (reqs.map (substExp name rhs)) (ens.map (substExp name rhs))
  | .AssertQuery mode body => .AssertQuery mode (substStm name rhs body)
  | .AssertCompute e => .AssertCompute (substExp name rhs e)
  | .AssertLean e => .AssertLean (substExp name rhs e)
  | .Assume e => .Assume (substExp name rhs e)
  | .Assign lhs lhsTy e lhsIsInit =>
    .Assign lhs lhsTy (substExp name rhs e) lhsIsInit
  | .DeadEnd stm => .DeadEnd (substStm name rhs stm)
  | .Return e => .Return (e.map (substExp name rhs))
  | .BreakOrContinue label isBreak => .BreakOrContinue label isBreak
  | .If cond b1 b2 =>
    .If (substExp name rhs cond) (substStm name rhs b1) (b2.map (substStm name rhs))
  | .Loop isFor label cond body invs decrease =>
    let cond' := cond.map (fun (s, e) => (substStm name rhs s, substExp name rhs e))
    let invs' := invs.map (fun inv => { inv with body := substExp name rhs inv.body })
    let decrease' := decrease.map (substExp name rhs)
    .Loop isFor label cond' (substStm name rhs body) invs' decrease'
  | .OpenInvariant stm => .OpenInvariant (substStm name rhs stm)
  | .ClosureInner body => .ClosureInner (substStm name rhs body)
  | .Block stms => .Block (stms.map (substStm name rhs))
  | .Reveal fn fuel => .Reveal fn fuel

partial def renameStmVar (src dst : String) : Stm → Stm :=
  substStm src (.Var dst)

def applyNameSubstsExp (subs : List (String × String)) (e : Exp) : Exp :=
  subs.foldl (fun acc (src, dst) => substExp src (.Var dst) acc) e

def applyNameSubstsStm (subs : List (String × String)) (s : Stm) : Stm :=
  subs.foldl (fun acc (src, dst) => renameStmVar src dst acc) s

/-! ## Statement normalization passes -/

partial def stripSingletonBlocks : Stm → Stm
  | .Block [s] => stripSingletonBlocks s
  | s => s

def isTempName (s : String) : Bool :=
  if s.startsWith "tmp" then
    let tail := s.drop 3
    !tail.isEmpty && tail.all Char.isDigit
  else
    false

def lvalueVarName? : LValue → Option String
  | .Var s => some s
  | _ => none

/-- Is the call expression `Call fn ...` a "pure builtin"?  Builtins here
    are language-specific recognizer shapes (e.g. `Vec.len`, `Seq` views)
    supplied by the caller via `isPureCallName`, keeping this module free
    of translator-side name conventions. -/
private def isPureBuiltinCallExp (isPureCallName : Ident → Bool) : Exp → Bool
  | .Call fn _ _ => isPureCallName (CallFun.name fn)
  | _ => false
  -- `CallFun.name` yields `Ident` (= `Lean.Name`), matching the caller
  -- predicate type so the caller can use library-shape checks directly
  -- without stringifying.

def tempAssignFromPrefix (isPureCallName : Ident → Bool) : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name =>
        if !isTempName name then none
        else match rhs with
          | .Call _ _ _ =>
            if isPureBuiltinCallExp isPureCallName rhs then some (name, rhs) else none
          | _ => some (name, rhs)
      | none => none
    | _ => none

def guardTempAssignFromPrefix : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name => if isTempName name then some (name, rhs) else none
      | none => none
    | _ => none

def dropCondTempAssignFromPrefix (isPureCallName : Ident → Bool) : Stm → Option String
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name =>
        if !isTempName name then none
        else match rhs with
          | .Call _ _ _ =>
            if isPureBuiltinCallExp isPureCallName rhs then some name else none
          | _ => some name
      | none => none
    | _ => none

def isEmptyElse (b2 : Option Stm) : Bool :=
  match b2 with
  | none => true
  | some (Stm.Block []) => true
  | _ => false

def breakGuardFromPrefix : Stm → Option Exp
  | s =>
    match stripSingletonBlocks s with
    | .If (.Unary .Not guard) (.BreakOrContinue none true) b2 =>
      if isEmptyElse b2 then some guard else none
    | _ => none

def splitGuardTempPrefix (stms : List Stm) : List (String × Exp) × List Stm :=
  let rec go (subsRev : List (String × Exp)) (rest : List Stm) :
      List (String × Exp) × List Stm :=
    match rest with
    | s :: tail =>
      match guardTempAssignFromPrefix s with
      | some sub => go (sub :: subsRev) tail
      | none => (subsRev.reverse, rest)
    | [] => (subsRev.reverse, [])
  go [] stms

def splitDropCondTempPrefix (isPureCallName : Ident → Bool) (stms : List Stm) :
    List String × List Stm :=
  let rec go (namesRev : List String) (rest : List Stm) :
      List String × List Stm :=
    match rest with
    | s :: tail =>
      match dropCondTempAssignFromPrefix isPureCallName s with
      | some n => go (n :: namesRev) tail
      | none => (namesRev.reverse, rest)
    | [] => (namesRev.reverse, [])
  go [] stms

def assignFromPrefix : Stm → Option (String × Exp)
  | s =>
    match stripSingletonBlocks s with
    | .Assign lhs _ rhs true =>
      match lvalueVarName? lhs with
      | some name => some (name, rhs)
      | none => none
    | _ => none

def splitAssignPrefix (stms : List Stm) : List (String × Exp) × List Stm :=
  let rec go (subsRev : List (String × Exp)) (rest : List Stm) :
      List (String × Exp) × List Stm :=
    match rest with
    | s :: tail =>
      match assignFromPrefix s with
      | some sub => go (sub :: subsRev) tail
      | none => (subsRev.reverse, rest)
    | [] => (subsRev.reverse, [])
  go [] stms

partial def flattenSeqBlocks : List Stm → List Stm
  | [] => []
  | (.Block stms) :: rest => flattenSeqBlocks stms ++ flattenSeqBlocks rest
  | s :: rest => s :: flattenSeqBlocks rest

def extractLoopGuardFromBody : Stm → Option (Exp × Stm)
  | .Block stms =>
    let linear := (flattenSeqBlocks stms).map stripSingletonBlocks
    let (subs, rest) := splitGuardTempPrefix linear
    match rest with
    | s :: tail =>
      match breakGuardFromPrefix s with
      | some guard => some (substExps subs guard, Stm.Block tail)
      | none => none
    | [] => none
  | _ => none

private partial def isEmptyProofShell : Stm → Bool
  | .Block [] => true
  | .Block [s] => isEmptyProofShell s
  | _ => false

mutual
  private partial def recoverComputeProofStm : Stm → Stm
    | .AssertQuery mode body => .AssertQuery mode (recoverComputeProofStm body)
    | .DeadEnd stm => .DeadEnd (recoverComputeProofStm stm)
    | .If cond b1 b2 =>
      .If cond (recoverComputeProofStm b1) (b2.map recoverComputeProofStm)
    | .Loop isFor label cond body invs decrease =>
      let cond' := cond.map (fun (s, e) => (recoverComputeProofStm s, e))
      .Loop isFor label cond' (recoverComputeProofStm body) invs decrease
    | .OpenInvariant stm => .OpenInvariant (recoverComputeProofStm stm)
    | .ClosureInner body => .ClosureInner (recoverComputeProofStm body)
    | .Block stms => .Block (recoverComputeProofs stms)
    | s => s

  partial def recoverComputeProofs : List Stm → List Stm
    | proofShell :: (.Assume e) :: rest =>
      if isEmptyProofShell proofShell then
        .AssertCompute e :: recoverComputeProofs rest
      else
        recoverComputeProofStm proofShell :: recoverComputeProofs ((.Assume e) :: rest)
    | s :: rest => recoverComputeProofStm s :: recoverComputeProofs rest
    | [] => []
end

-- Kept separate from `expVarRefs` intentionally: a short-circuiting
-- membership test avoids the O(n) collect-then-`List.contains` cost on
-- large expression bodies (see `stmMentionsVar` below, which calls this
-- once per statement).
partial def expMentionsVar (target : String) : Exp → Bool
  | .Var x => x == target
  | .Call _ _ args => args.any (expMentionsVar target)
  | .CallLambda body args =>
    expMentionsVar target body || args.any (expMentionsVar target)
  | .StructCtor _ fields => fields.any (fun (_, e) => expMentionsVar target e)
  | .EnumCtor _ _ fields => fields.any (fun (_, e) => expMentionsVar target e)
  | .TupleCtor _ elems => elems.any (expMentionsVar target)
  | .Unary _ e => expMentionsVar target e
  | .Binary _ e1 e2 => expMentionsVar target e1 || expMentionsVar target e2
  | .If c t f => expMentionsVar target c || expMentionsVar target t || expMentionsVar target f
  | .Bind (.Let _ _ e) body => expMentionsVar target e || expMentionsVar target body
  | .Bind (.Quant _ _ _) body => expMentionsVar target body
  | .Bind (.Lambda _) body => expMentionsVar target body
  | .ArrayLiteral elems => elems.any (expMentionsVar target)
  | .MatchBlock (scrut, _) body => expMentionsVar target scrut || expMentionsVar target body
  | .Const _ _ => false

partial def stmMentionsVar (target : String) : Stm → Bool
  | .Call _ _ args => args.any (expMentionsVar target)
  | .Assert e | .AssertCompute e | .AssertLean e | .Assume e => expMentionsVar target e
  | .AssertBitVector reqs enss =>
    reqs.any (expMentionsVar target) || enss.any (expMentionsVar target)
  | .AssertQuery _ body => stmMentionsVar target body
  | .Assign lhs _ rhs _ =>
    (match lvalueVarName? lhs with | some n => n == target | none => false) ||
    expMentionsVar target rhs
  | .DeadEnd s | .OpenInvariant s | .ClosureInner s => stmMentionsVar target s
  | .Reveal .. => false
  | .Return e? => e?.map (expMentionsVar target) |>.getD false
  | .BreakOrContinue _ _ => false
  | .If cond b1 b2 =>
    expMentionsVar target cond ||
      stmMentionsVar target b1 ||
      (b2.map (stmMentionsVar target)).getD false
  | .Loop _ _ cond body invs decrease =>
    let condM := match cond with
      | some (s, e) => stmMentionsVar target s || expMentionsVar target e
      | none => false
    condM || invs.any (fun inv => expMentionsVar target inv.body) ||
      decrease.any (expMentionsVar target) || stmMentionsVar target body
  | .Block stms => stms.any (stmMentionsVar target)

mutual
partial def inlineTempsInStm (isPureCallName : Ident → Bool) : Stm → Stm
  | .AssertQuery mode body => .AssertQuery mode (inlineTempsInStm isPureCallName body)
  | .DeadEnd stm => .DeadEnd (inlineTempsInStm isPureCallName stm)
  | .If cond b1 b2 =>
    .If cond (inlineTempsInStm isPureCallName b1)
      (b2.map (inlineTempsInStm isPureCallName))
  | .Loop isFor label cond body invs decrease =>
    let cond' := cond
    let body' := match body with
      | .Block stms => .Block (inlineTemps isPureCallName stms)
      | _ => inlineTempsInStm isPureCallName body
    .Loop isFor label cond' body' invs decrease
  | .OpenInvariant stm => .OpenInvariant (inlineTempsInStm isPureCallName stm)
  | .ClosureInner body => .ClosureInner (inlineTempsInStm isPureCallName body)
  | .Block stms => .Block (inlineTemps isPureCallName stms)
  | .Reveal fn fuel => .Reveal fn fuel
  | s => s

partial def inlineTemps (isPureCallName : Ident → Bool) : List Stm → List Stm
  | [] => []
  | stm :: rest =>
    let rest' := inlineTemps isPureCallName rest
    match tempAssignFromPrefix isPureCallName stm with
    | some (lhs, rhs) =>
      if rest'.any (stmMentionsVar lhs) then
        rest'.map (substStm lhs rhs)
      else
        inlineTempsInStm isPureCallName stm :: rest'
    | none => inlineTempsInStm isPureCallName stm :: rest'
end

mutual
  /-- Recursive helper: applies `normalizeStms` to nested statement lists
      (Block contents, Loop bodies, If branches), and at each `.Loop` site
      tries to populate `Loop.cond` from a body-prefix guard via
      `extractLoopGuardFromBody`. -/
  partial def normalizeStm (isPureCallName : Ident → Bool) : Stm → Stm
    | .Block stms => .Block (normalizeStms isPureCallName stms)
    | .If cond b1 b2 =>
      .If cond (normalizeStm isPureCallName b1)
        (b2.map (normalizeStm isPureCallName))
    | .Loop isFor label cond body invs dec =>
      let cond' := cond.map (fun (s, e) => (normalizeStm isPureCallName s, e))
      let body' := normalizeStm isPureCallName body
      match cond', extractLoopGuardFromBody body' with
      | none, some (g, b'') =>
        -- Hoist body-prefix guard into Loop.cond. The guard `g` already
        -- has any tmp prefix substituted in by `extractLoopGuardFromBody`,
        -- so the cond's prefix-Stm slot stays empty.
        .Loop isFor label (some (.Block [], g)) (normalizeStm isPureCallName b'') invs dec
      | _, _ => .Loop isFor label cond' body' invs dec
    | .AssertQuery m b => .AssertQuery m (normalizeStm isPureCallName b)
    | .DeadEnd b => .DeadEnd (normalizeStm isPureCallName b)
    | .OpenInvariant b => .OpenInvariant (normalizeStm isPureCallName b)
    | .ClosureInner b => .ClosureInner (normalizeStm isPureCallName b)
    | s => s

  /-- Apply the four list-level normalization passes (inline temps, recover
      compute-proof shells, flatten nested top-level Blocks, strip singleton
      Blocks) to a statement list, then descend into each statement. -/
  partial def normalizeStms (isPureCallName : Ident → Bool)
      (stms : List Stm) : List Stm :=
    let normalized :=
      (flattenSeqBlocks (recoverComputeProofs (inlineTemps isPureCallName stms))).map
        stripSingletonBlocks
    normalized.map (normalizeStm isPureCallName)
end

/-- Single VLIR-level normalization pre-pass run once per body before
    `stmToBoole`. After this pass:
      * `stmListToBoole` does not need to renormalize its statement list, and
      * `stmToBoole`'s `.Loop` handler can read `Loop.cond` directly instead
        of recovering it from a body prefix.
    Centralizing the passes here is what lets the local-variable filter be
    a plain `stmMentionsVar` check — the post-pass body already reflects
    every tmp the translator will end up dropping. -/
def normalizeBody (isPureCallName : Ident → Bool) (body : Stm) : Stm :=
  match body with
  | .Block stms => .Block (normalizeStms isPureCallName stms)
  | s => normalizeStm isPureCallName s

private def isDecreaseArtifact : Stm → Bool
  | .Assign (.Var name) _ _ _ => name.startsWith "decrease"
  | .Call fn _ _ => toString fn |>.startsWith "CheckDecrease"
  | .Assert (.Call fn _ _) =>
    toString (CallFun.name fn) |>.startsWith "CheckDecrease"
  | .Assert (.Var name) => name.startsWith "CheckDecrease"
  | _ => false

partial def stripDecreaseArtifacts : Stm → Stm
  | .Block stms =>
    .Block (stms.filter (!isDecreaseArtifact ·) |>.map stripDecreaseArtifacts)
  | .If cond b1 b2 =>
    .If cond (stripDecreaseArtifacts b1) (b2.map stripDecreaseArtifacts)
  | .DeadEnd stm => .DeadEnd (stripDecreaseArtifacts stm)
  | .Loop isFor label cond body invs dec =>
    .Loop isFor label cond (stripDecreaseArtifacts body) invs dec
  | stm => stm

private partial def hasReturnStm : Stm → Bool
  | .Return _ => true
  | .Block stms => stms.any hasReturnStm
  | .If _ b1 b2 => hasReturnStm b1 || (b2.map hasReturnStm |>.getD false)
  | .DeadEnd stm => hasReturnStm stm
  | _ => false

private def isAssumeFalse : Stm → Bool
  | .Assume (.Const (.Bool false) _) => true
  | _ => false

/-- True if any statement in the list (recursing into nested `Block` / `If`
    branches) is a `Return`. Equivalent to `stms.any hasReturnStm` since
    `hasReturnStm` already descends through those two structural cases. -/
private def blockHasReturn (stms : List Stm) : Bool :=
  stms.any hasReturnStm

partial def stripReturnAssumeFalse : List Stm → List Stm
  | [] => []
  | (.Return e) :: rest =>
    .Return e :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
  | (.Block stms) :: rest =>
    let stripped := .Block (stripReturnAssumeFalse stms)
    if blockHasReturn stms then
      stripped :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
    else
      stripped :: stripReturnAssumeFalse rest
  | (.If cond b1 b2) :: rest =>
    let b1' := stripReturnDeep b1
    let b2' := b2.map stripReturnDeep
    let ifHasRet := hasReturnStm b1 || (b2.map hasReturnStm |>.getD false)
    let stripped := .If cond b1' b2'
    if ifHasRet then
      stripped :: (rest.filter (!isAssumeFalse ·) |> stripReturnAssumeFalse)
    else
      stripped :: stripReturnAssumeFalse rest
  | s :: rest => s :: stripReturnAssumeFalse rest
where
  -- Deep traversal that rewrites any nested `Block` via
  -- `stripReturnAssumeFalse`, but for `.Loop` it only descends into the
  -- loop body as a whole (`stripReturnDeep body`) without further
  -- `stripReturnAssumeFalse` on its statement list. Verus does not emit
  -- `return; assume false;` pairs inside loop bodies — early returns are
  -- lifted out of the loop during SST lowering — so the simpler
  -- traversal is sufficient today. If that assumption changes, call
  -- `stripReturnAssumeFalse` on the loop body's block contents too.
  stripReturnDeep : Stm → Stm
    | .Block stms => .Block (stripReturnAssumeFalse stms)
    | .If cond b1 b2 => .If cond (stripReturnDeep b1) (b2.map stripReturnDeep)
    | .DeadEnd stm => .DeadEnd (stripReturnDeep stm)
    | .Loop isFor label cond body invs dec =>
      .Loop isFor label cond (stripReturnDeep body) invs dec
    | s => s

end VerusLean.Boole.Normalize
