/-
  Boole.IntPromotion — int-promotability inference for `usize`/`isize`
  locals and for-loop binders.

  Rust `usize`/`isize` lower to fixed-width bitvectors by default,
  which is a precise model when the value participates in wrapping
  arithmetic or bit-level operations.  When a counter is only used as a
  sequence index or compared against `Sequence.length`, the bv encoding
  forces every use site through an uninterpreted `bv64_to_int_u(_)`
  cast, and the solver can no longer relate the counter's known range
  to the sequence's length.

  This pass classifies `usize`/`isize` locals and for-loop binders by
  their use sites and reports which ones can safely be retyped to
  `Int`.  A name is reported iff:

    • At least one use is a "qualifying" use — sequence index, sequence
      mutation/slicing slot, or comparison against a length call.
    • No use is in a "rejecting" use — bitwise op, explicit bv cast,
      callee parameter that expects bv, an opaque arg slot, assignment
      into a bv-typed non-candidate target, or an assignment dependency
      connected to a rejected/non-int candidate.

  The result is a `Std.HashSet String` of names whose `Typ` should be
  rewritten from `USize / ISize` to `Int` before the rest of the
  translator runs.  Procedure inputs and mut-ref outputs are never in
  the result — they cross call boundaries.

  Box / Clip / Unbox wrappers are transparent to the classifier (they
  are Verus' overflow-check / type-erasure scaffolding).
-/
import Std.Data.HashSet
import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Coercions
import VerusLean.VLIR.Boole.ForLoop
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.IntPromotion

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.ForLoop
open VerusLean.Boole.Names

/-! ## Type classification helpers -/

private def isCandidateTyp : Typ → Bool
  | .USize | .ISize => true
  | .Decorated _ inner => isCandidateTyp inner
  | _ => false

/-! ## Use-site classification

    The pass walks the body and, for each occurrence of a candidate
    name, decides whether the surrounding context is qualifying,
    rejecting, or neutral.  Box / Clip / Unbox are transparent so the
    classifier always recurses on the wrapped expression. -/

inductive Ctx where
  | seqIdx        -- index slot of a Sequence/Vec/Slice/Array index/update
  | seqLenCmp     -- compared against a length call
  | safe          -- generic int-safe context (arith, comparison, for-bound)
  | reject        -- bitwise op, explicit bv cast, opaque slot
deriving Inhabited, BEq

private def isLengthCallName (name : Ident) : Bool :=
  isSeqLenSpecName name || isVecLenSpecName name || isVecLenExecName name
    || isSliceLenSpecName name || isSliceLenExecName name

private def isIndexCallName (name : Ident) : Bool :=
  isVecIndexSpecName name || isVecIndexExecName name
    || isArrayIndexGetName name || isSliceIndexGetName name

private def callFunNameIs (fn : CallFun) (p : Ident → Bool) : Bool :=
  p (CallFun.name fn)

private def isLengthExp : Exp → Bool
  | .Call fn _ _ => callFunNameIs fn isLengthCallName
  | .Unary .Length _ => true
  | .Unary (.Box _) e | .Unary (.Unbox _) e | .Unary (.Clip _ _) e =>
    isLengthExp e
  | _ => false

/-- Return true if the call name is a known opaque/transparent helper
    that should not be treated as a "user procedure call" — these flow
    through to one of the dedicated translator arms (`isViewName`,
    `isCloneExecName`, etc.) without forcing a bv parameter. -/
private def isTransparentCallName (name : Ident) : Bool :=
  isViewName name || isBoxNewName name || isCloneExecName name
    || isArrayAsSliceName name || isSliceIntoVecName name
    || isClonedName name

private def seqCallArgCtxs? (fname : String) : Option (List Ctx) :=
  if fname == "Seq_index" then
    some [.safe, .seqIdx]
  else if fname == "Seq_update" then
    some [.safe, .seqIdx, .reject]
  else if fname == "Seq_take" || fname == "Seq_skip"
       || fname == "Seq_lib_remove" then
    some [.safe, .seqIdx]
  else if fname == "Seq_subrange" then
    some [.safe, .seqIdx, .seqIdx]
  else if fname == "Seq_push" || fname == "Seq_lib_contains" then
    some [.safe, .reject]
  else if fname == "Seq_add" || fname == "Seq_lib_zip_with" then
    some [.safe, .safe]
  else if fname == "Seq_first" || fname == "Seq_last"
       || fname == "Seq_lib_drop_last" then
    some [.safe]
  else if fname == "Seq_empty" then
    some []
  else
    none

/-! ## Per-pass state

    `qualifying` records candidates with at least one seq-idx/length
    use.  `rejected` records candidates that hit a rejecting context.
    `assignDeps` records, for every assignment `k := rhs`, the set of
    other candidates referenced anywhere in `rhs`; used in the fixpoint
    pass to propagate rejection through assignment chains.  Rejection
    propagates both directions: a rejected RHS taints the assigned LHS,
    and a rejected LHS means the RHS was used in a bv-forced context.
-/

structure State where
  candidates : Std.HashSet String := ∅
  qualifying : Std.HashSet String := ∅
  rejected   : Std.HashSet String := ∅
  /-- `assignDeps[k] = {j₁, j₂, …}` — every candidate `jᵢ` appearing in
      any RHS assigned into `k`. -/
  assignDeps : Std.HashMap String (Std.HashSet String) := ∅
deriving Inhabited

private def State.isCandidate (s : State) (name : String) : Bool :=
  s.candidates.contains name

private def State.markQualifying (s : State) (name : String) : State :=
  if s.isCandidate name then { s with qualifying := s.qualifying.insert name }
  else s

private def State.markRejected (s : State) (name : String) : State :=
  if s.isCandidate name then { s with rejected := s.rejected.insert name }
  else s

private def State.addAssignDep (s : State) (lhs : String) (rhsVar : String) : State :=
  if s.isCandidate lhs && s.isCandidate rhsVar && lhs ≠ rhsVar then
    let cur := s.assignDeps.getD lhs ∅
    { s with assignDeps := s.assignDeps.insert lhs (cur.insert rhsVar) }
  else s

private def isActiveCandidate (s : State) (shadowed : Std.HashSet String) (name : String) : Bool :=
  s.isCandidate name && !shadowed.contains name

private def shadowBinders (shadowed : Std.HashSet String) (vars : List (String × Typ)) :
    Std.HashSet String :=
  vars.foldl (fun acc (v, _) => acc.insert v) shadowed

/-! ## Variable collection within an expression -/

mutual
  /-- Collect every candidate variable name appearing in `e`. -/
  private partial def candidateVarsInExp (s : State) (e : Exp) : Std.HashSet String :=
    candidateVarsInExpAux s ∅ ∅ e

  private partial def candidateVarsInExpAux
      (s : State) (shadowed : Std.HashSet String) (acc : Std.HashSet String) :
      Exp → Std.HashSet String
    | .Var name => if isActiveCandidate s shadowed name then acc.insert name else acc
    | .Const _ _ => acc
    | .Call _ _ args => args.foldl (candidateVarsInExpAux s shadowed) acc
    | .CallLambda body args =>
      let acc := candidateVarsInExpAux s shadowed acc body
      args.foldl (candidateVarsInExpAux s shadowed) acc
    | .Unary _ e => candidateVarsInExpAux s shadowed acc e
    | .Binary _ a b =>
      let acc := candidateVarsInExpAux s shadowed acc a
      candidateVarsInExpAux s shadowed acc b
    | .If c t f =>
      let acc := candidateVarsInExpAux s shadowed acc c
      let acc := candidateVarsInExpAux s shadowed acc t
      candidateVarsInExpAux s shadowed acc f
    | .Bind bind body =>
      match bind with
      | .Let v _ rhs =>
        let acc := candidateVarsInExpAux s shadowed acc rhs
        candidateVarsInExpAux s (shadowed.insert v) acc body
      | .Quant _ vars trigs =>
        let shadowed' := shadowBinders shadowed vars
        let acc := trigs.foldl
          (fun acc group => group.foldl (candidateVarsInExpAux s shadowed') acc) acc
        candidateVarsInExpAux s shadowed' acc body
      | .Lambda vars =>
        candidateVarsInExpAux s (shadowBinders shadowed vars) acc body
      | .Choose vars pred =>
        let shadowed' := shadowBinders shadowed vars
        let acc := candidateVarsInExpAux s shadowed' acc pred
        candidateVarsInExpAux s shadowed' acc body
    | .ArrayLiteral elts => elts.foldl (candidateVarsInExpAux s shadowed) acc
    | .StructCtor _ fields =>
      fields.foldl (fun acc (_, e) => candidateVarsInExpAux s shadowed acc e) acc
    | .EnumCtor _ _ data =>
      data.foldl (fun acc (_, e) => candidateVarsInExpAux s shadowed acc e) acc
    | .TupleCtor _ data => data.foldl (candidateVarsInExpAux s shadowed) acc
    | .MatchBlock (scr, _) body =>
      let acc := candidateVarsInExpAux s shadowed acc scr
      candidateVarsInExpAux s shadowed acc body
end

/-! ## Main classifier

    Walk an expression with a surrounding context.  At every `Var k`
    that is a candidate, mark `k` as qualifying or rejected per `ctx`.
    At every recursive position, decide the child's context based on
    the operator and recurse. -/

mutual
  /-- Classify an expression in context `ctx`.  Updates the state. -/
  partial def visitExp (s : State) (ctx : Ctx) (e : Exp) : State :=
    visitExpAux s ∅ ctx e

  private partial def visitExpAux
      (s : State) (shadowed : Std.HashSet String) (ctx : Ctx) : Exp → State
    | .Var name =>
      if isActiveCandidate s shadowed name then
        match ctx with
        | .reject => s.markRejected name
        | .seqIdx | .seqLenCmp => s.markQualifying name
        | .safe => s
      else s
    | .Const _ _ => s
    -- Box / Clip / Unbox are translator-injected wrappers; transparent.
    | .Unary (.Box _) e | .Unary (.Unbox _) e | .Unary (.Clip _ _) e =>
      visitExpAux s shadowed ctx e
    | .Unary .Not e => visitExpAux s shadowed .safe e
    -- Bitwise NOT and any other unary operator that requires bv typing.
    | .Unary (.BitNot _) e => visitExpAux s shadowed .reject e
    -- Triggers, projections, IsVariant, HasType, Old: opaque/safe wrappers
    -- that don't constrain numeric typing of their operand.
    | .Unary _ e => visitExpAux s shadowed .safe e
    | .Binary op a b => visitBinary s shadowed ctx op a b
    | .If c t f =>
      let s := visitExpAux s shadowed .safe c
      let s := visitExpAux s shadowed ctx t
      visitExpAux s shadowed ctx f
    | .Call fn _ args => visitCall s shadowed ctx fn args
    | .CallLambda body args =>
      -- Opaque body — conservatively reject any candidate appearing in
      -- the body or args.
      let s := visitExpAux s shadowed .reject body
      args.foldl (fun s e => visitExpAux s shadowed .reject e) s
    | .Bind bind body =>
      match bind with
      | .Let v _ rhs =>
        let s := visitExpAux s shadowed .safe rhs
        visitExpAux s (shadowed.insert v) ctx body
      | .Quant _ vars trigs =>
        let shadowed' := shadowBinders shadowed vars
        let s := trigs.foldl
          (fun s group => group.foldl (fun s e => visitExpAux s shadowed' .safe e) s) s
        visitExpAux s shadowed' .safe body
      | .Lambda vars =>
        visitExpAux s (shadowBinders shadowed vars) .safe body
      | .Choose vars pred =>
        let shadowed' := shadowBinders shadowed vars
        let s := visitExpAux s shadowed' .safe pred
        visitExpAux s shadowed' ctx body
    | .ArrayLiteral elts =>
      elts.foldl (fun s e => visitExpAux s shadowed .safe e) s
    | .StructCtor _ fields =>
      -- Candidate stored into a struct field is assumed bv-typed (we
      -- can't see the field type here).  Reject conservatively.
      fields.foldl (fun s (_, e) => visitExpAux s shadowed .reject e) s
    | .EnumCtor _ _ data =>
      data.foldl (fun s (_, e) => visitExpAux s shadowed .reject e) s
    | .TupleCtor _ data => data.foldl (fun s e => visitExpAux s shadowed .reject e) s
    | .MatchBlock (scr, _) body =>
      let s := visitExpAux s shadowed .safe scr
      visitExpAux s shadowed ctx body

  partial def visitBinary
      (s : State) (shadowed : Std.HashSet String) (ctx : Ctx)
      (op : BinaryOp) (a b : Exp) : State :=
    match op with
    | .Bitwise _ _ =>
      -- bitwise op forces bv on every operand.
      let s := visitExpAux s shadowed .reject a
      visitExpAux s shadowed .reject b
    | .Arith _ _ =>
      -- pure arithmetic — propagate the surrounding context, but a bare
      -- arithmetic context (not seq-idx, not seq-len-cmp) is just `safe`.
      let childCtx : Ctx := match ctx with
        | .seqIdx | .seqLenCmp => ctx
        | _ => .safe
      let s := visitExpAux s shadowed childCtx a
      visitExpAux s shadowed childCtx b
    | .Eq _ | .Ne | .Inequality _ =>
      -- comparisons: each side becomes seqLenCmp if the other side is a
      -- length call, otherwise plain `safe`.
      let aCtx : Ctx := if isLengthExp b then .seqLenCmp else .safe
      let bCtx : Ctx := if isLengthExp a then .seqLenCmp else .safe
      let s := visitExpAux s shadowed aCtx a
      visitExpAux s shadowed bCtx b
    | .ExtEq _ _ =>
      let s := visitExpAux s shadowed .safe a
      visitExpAux s shadowed .safe b
    | .Index =>
      let s := visitExpAux s shadowed .safe a
      visitExpAux s shadowed .seqIdx b
    | .And | .Or | .Xor | .Implies =>
      let s := visitExpAux s shadowed .safe a
      visitExpAux s shadowed .safe b

  partial def visitCall
      (s : State) (shadowed : Std.HashSet String) (ctx : Ctx)
      (fn : CallFun) (args : List Exp) : State :=
    let name := CallFun.name fn
    let fnameStr := identToBoole name
    -- Sequence / Vec / Slice / Array index calls — first arg is the
    -- container, second is the index.  Mark the index slot as seqIdx.
    if isIndexCallName name then
      visitIndexedCall s shadowed args
    -- Length calls: container in arg 0, no index slot.
    else if isLengthCallName name then
      args.foldl (fun s e => visitExpAux s shadowed .safe e) s
    -- Box / clone / view / slice-into-vec / cloned: transparent.
    else if isTransparentCallName name then
      args.foldl (fun s e => visitExpAux s shadowed ctx e) s
    -- Sequence operations dispatched on string name in `expToBoole`.
    -- Only true index/count positions are qualifying. Element values and
    -- whole-sequence arguments are not evidence that a name is an index-like
    -- counter, so they remain safe or rejecting according to their slot.
    else
      match seqCallArgCtxs? fnameStr with
      | some argCtxs => visitCallArgs s shadowed args argCtxs
      | none =>
        if isWrappingAddName name then
          -- bv-only — both args force bv.
          args.foldl (fun s e => visitExpAux s shadowed .reject e) s
        else
          -- Opaque user/std call.  Conservatively reject any candidate
          -- appearing as an argument: we can't see the param types here, and
          -- even if we could the param is most likely bv-typed.
          args.foldl (fun s e => visitExpAux s shadowed .reject e) s

  /-- Visit a known call by its per-argument contexts.  Arity mismatches
      are treated as opaque/rejecting instead of partially applying a
      stale signature. -/
  partial def visitCallArgs
      (s : State) (shadowed : Std.HashSet String) : List Exp → List Ctx → State
    | [], [] => s
    | arg :: args, ctx :: ctxs =>
      visitCallArgs (visitExpAux s shadowed ctx arg) shadowed args ctxs
    | args, _ =>
      args.foldl (fun s e => visitExpAux s shadowed .reject e) s

  /-- An indexed call has two args: container and index.  The index
      argument is in seqIdx context; the container is safe. -/
  partial def visitIndexedCall
      (s : State) (shadowed : Std.HashSet String) : List Exp → State
    | [container, idx] =>
      let s := visitExpAux s shadowed .safe container
      visitExpAux s shadowed .seqIdx idx
    | args =>
      -- Unexpected arity — conservatively reject candidates appearing
      -- anywhere.
      args.foldl (fun s e => visitExpAux s shadowed .reject e) s
end

/-! ## Statement walker -/

mutual
  partial def visitStm (s : State) : Stm → State
    | .Assert e => visitExp s .safe e
    | .AssertBitVector requires ensures =>
      -- The whole expression is bit-vector assert — every candidate var
      -- referenced inside is forced bv.
      let s := requires.foldl (fun s e => visitExp s .reject e) s
      ensures.foldl (fun s e => visitExp s .reject e) s
    | .AssertCompute e => visitExp s .safe e
    | .AssertLean e => visitExp s .safe e
    | .Assume e => visitExp s .safe e
    | .AssertQuery _ body => visitStm s body
    | .Assign lhs lhsTy rhs _ =>
      let rhsCtx : Ctx :=
        match lhs.baseVar? with
        | some lhsName =>
          if s.isCandidate lhsName then .safe
          else if (bitInfoOfTyp lhsTy).isSome then .reject
          else .safe
        | none =>
          if (bitInfoOfTyp lhsTy).isSome then .reject else .safe
      let s := visitExp s rhsCtx rhs
      match lhs.baseVar? with
      | some lhsName =>
        -- Add edges from every candidate referenced in rhs into lhsName.
        let rhsVars := candidateVarsInExp s rhs
        let s := rhsVars.fold (fun acc j => acc.addAssignDep lhsName j) s
        s
      | none => s
    | .DeadEnd stm => visitStm s stm
    | .Return (some e) => visitExp s .safe e
    | .Return none => s
    | .BreakOrContinue _ _ => s
    | .Reveal _ _ => s
    | .Call fn _ args =>
      -- `Std_specs_Core_index_set(container, index, value)` is the
      -- statement-form of `container[index] = value`.  The index slot
      -- is a sequence-index position — qualifying — and the value slot
      -- is a generic stored value (rejected unless the value's type is
      -- known not to force bv).  Conservatively: container is safe,
      -- index is seqIdx, value is reject.  For any other Stm.Call, no
      -- per-slot signatures are available, so fall back to rejecting
      -- every candidate appearing in any arg.
      if isIndexSetName fn then
        match args with
        | [container, idx, value] =>
          let s := visitExp s .safe container
          let s := visitExp s .seqIdx idx
          visitExp s .reject value
        | _ => args.foldl (fun s e => visitExp s .reject e) s
      else
        args.foldl (fun s e => visitExp s .reject e) s
    | .If cond b1 b2 =>
      let s := visitExp s .safe cond
      let s := visitStm s b1
      match b2 with
      | some b2 => visitStm s b2
      | none => s
    | .Loop _ _ cond body invs decreases =>
      let s := match cond with
        | some (preStm, e) =>
          let s := visitStm s preStm
          visitExp s .safe e
        | none => s
      let s := invs.foldl (fun s inv => visitExp s .safe inv.body) s
      let s := decreases.foldl (fun s e => visitExp s .safe e) s
      visitStm s body
    | .OpenInvariant body => visitStm s body
    | .ClosureInner body => visitStm s body
    | .Block stms => visitStms s stms

  partial def visitStms (s : State) : List Stm → State
    | [] => s
    | stms =>
      -- Check whether this Block opens a recovered for-loop — if so,
      -- the for-loop binder is itself a candidate (for `usize`/`isize`
      -- binders) and the loop bound is a `safe` int comparison context.
      match recoverForLoop? stms with
      | some loop =>
        let s :=
          if isCandidateTyp loop.loopVarTy then
            { s with candidates := s.candidates.insert loop.loopVarName }
          else s
        let s := loop.preStms.foldl visitStm s
        let s := visitExp s .safe loop.startExp
        -- The endExp is the loop bound; treat as a length-comparison
        -- against the binder so the binder qualifies for promotion.
        let endIsLen := isLengthExp loop.endExp
        let binderCtx : Ctx := if endIsLen then .seqLenCmp else .safe
        let s := visitExp s binderCtx loop.endExp
        let s :=
          if isCandidateTyp loop.loopVarTy then
            -- The binder itself counts as compared against the bound;
            -- when the bound is a length call, that's a qualifying use.
            if endIsLen then s.markQualifying loop.loopVarName
            else s
          else s
        let s := loop.invariants.foldl (fun s inv => visitExp s .safe inv.body) s
        let s := loop.decrease.foldl (fun s e => visitExp s .safe e) s
        let s := visitStm s (.Block loop.userBody)
        loop.postStms.foldl visitStm s
      | none =>
        match stms with
        | [] => s
        | s' :: rest => visitStms (visitStm s s') rest
end

/-! ## Fixpoint propagation

    A candidate `k` is rejected if any candidate it depends on (via an
    assignment chain `k := … j …`) is rejected.  Conversely, if `k` is
    rejected, every candidate assigned into `k` has been used in a
    bv-forced context and is rejected as well.  Iterate until no new
    rejections appear. -/

private partial def propagateOnce (s : State) : State × Bool := Id.run do
  let mut s := s
  let mut changed := false
  for kEntry in s.assignDeps.toList do
    let (k, deps) := kEntry
    if s.rejected.contains k then
      for j in deps do
        if !s.rejected.contains j then
          s := { s with rejected := s.rejected.insert j }
          changed := true
    else
      let mut hit := false
      for j in deps do
        if s.rejected.contains j then hit := true; break
      if hit then
        s := { s with rejected := s.rejected.insert k }
        changed := true
  return (s, changed)

private partial def fixpoint (s : State) : State :=
  let (s', changed) := propagateOnce s
  if changed then fixpoint s' else s'

/-! ## Public entry point -/

/-- Compute the set of candidate names that should be promoted from
    `usize`/`isize` to `Int` based on body use sites.

    Inputs:
      • `locals` — `f.locals` (procedure source-declared locals).
      • `body`   — `f.body` (the un-normalized procedure body).

    The result includes both `usize`/`isize` locals and `usize`/`isize`
    for-loop binders that survive the rule. -/
def inferIntPromotableLocals
    (locals : List LocalDeclInfo) (body : Stm) : Std.HashSet String :=
  let initialCandidates : Std.HashSet String :=
    locals.foldl (fun acc decl =>
      if isCandidateTyp decl.ty then acc.insert decl.name else acc) ∅
  let initialState : State := { candidates := initialCandidates }
  let walked := visitStm initialState body
  let resolved := fixpoint walked
  -- Final: promoted = candidates ∩ qualifying \ rejected.
  resolved.candidates.fold (fun acc name =>
    if resolved.qualifying.contains name && !resolved.rejected.contains name then
      acc.insert name
    else acc) ∅

/-! ## Body / locals rewriters

    Once the inference returns a `HashSet` of promoted names, the
    translator can apply the typing change uniformly by:

      • rewriting every `Assign`'s `lhsTy` on a promoted name to `Int`,
      • rewriting every `LocalDeclInfo` of a promoted name to `Int`.

    The expression translator then sees `expected = some Int` at every
    use site (driven by the env and the assignment's lhsTy), and the
    Box/Clip short-circuit takes care of Verus' wrappers.

    For-loop binders are not in `f.locals`; the rewrite for them lives
    in `tryForLoopRecovery`, which consults `BuildCtx.promotedLocals`
    to decide whether to retype the binder. -/

private def promotedLhsTy (promoted : Std.HashSet String) (lhs : LValue) (ty : Typ) : Typ :=
  match lhs.baseVar? with
  | some name => if promoted.contains name then .Int else ty
  | none => ty

mutual
  /-- Rewrite every `Assign`'s `lhsTy` on a promoted name to `Int`. -/
  partial def rewriteBodyForPromoted (promoted : Std.HashSet String) : Stm → Stm
    | .Assign lhs lhsTy rhs lhsIsInit =>
      .Assign lhs (promotedLhsTy promoted lhs lhsTy) rhs lhsIsInit
    | .Block stms => .Block (stms.map (rewriteBodyForPromoted promoted))
    | .If cond b1 b2 =>
      .If cond (rewriteBodyForPromoted promoted b1)
        (b2.map (rewriteBodyForPromoted promoted))
    | .Loop isFor label cond body invs decreases =>
      let cond' := cond.map (fun (s, e) => (rewriteBodyForPromoted promoted s, e))
      .Loop isFor label cond' (rewriteBodyForPromoted promoted body) invs decreases
    | .DeadEnd s => .DeadEnd (rewriteBodyForPromoted promoted s)
    | .OpenInvariant s => .OpenInvariant (rewriteBodyForPromoted promoted s)
    | .ClosureInner s => .ClosureInner (rewriteBodyForPromoted promoted s)
    | .AssertQuery mode body => .AssertQuery mode (rewriteBodyForPromoted promoted body)
    | stm => stm
end

/-- Rewrite every promoted local's `Typ` to `Int`. -/
def rewriteLocalsForPromoted
    (promoted : Std.HashSet String) (locals : List LocalDeclInfo) : List LocalDeclInfo :=
  locals.map (fun decl =>
    if promoted.contains decl.name && isCandidateTyp decl.ty then
      { decl with ty := .Int }
    else decl)

private def isUnsignedCandidateTyp : Typ → Bool
  | .USize => true
  | .Decorated _ inner => isUnsignedCandidateTyp inner
  | _ => false

/-- The promoted names whose source type was `usize`, so `0 <= name` holds by
    construction.  Retyping to `Int` drops that guarantee, and a loop havocs
    the variable, so loops re-pin it as a synthesized invariant.  Must be
    called with the *pre-rewrite* locals, whose types still record signedness.
    `isize` locals are excluded: promoting them loses no such fact. -/
def unsignedPromotedLocals
    (promoted : Std.HashSet String) (locals : List LocalDeclInfo) : Std.HashSet String :=
  locals.foldl (fun acc decl =>
    if promoted.contains decl.name && isUnsignedCandidateTyp decl.ty then
      acc.insert decl.name
    else acc) ∅

end VerusLean.Boole.IntPromotion
