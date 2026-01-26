/-
  VLIR to Strata Core Translation (WIP)

  Translates the Verus-Lean IR (VLIR) to Strata Core AST.
-/

import Std.Data.HashMap
import Strata.Languages.Core.Program
import Strata.Languages.Core.Factory
import Strata.DL.Lambda.LExpr
import VerusLean.VLIR.Defs

namespace VerusLean

namespace ToCore

open Core
open Lambda

abbrev CoreExpr := Core.Expression.Expr
abbrev VarEnv := Std.HashMap String Typ -- global/free variables
abbrev BoundEnv := List (String × Typ) -- bound variables introduced by binders in quantifiers, lets, etc.

structure ToCoreCtx where
  -- A temporary flag, map `u32` to `int` when the file does not use bitvector ops.
  useIntU32 : Bool

/-! ## Utilities -/

-- Check if a character is valid in a Core identifier.
def isIdentChar (c : Char) : Bool :=
  c.isAlpha || c.isDigit || c == '_'

-- Sanitize an identifier for Core, as VLIR identifiers might contain invalid characters like `%`, `::`, `<`, `>`, etc.
def sanitizeIdent (s : String) : String :=
  let mapped := s.map fun c => if isIdentChar c then c else '_'
  match mapped.toList with
  | c :: _ => if c.isDigit then "_" ++ mapped else mapped
  | [] => "_"

def identToCore (i : Ident) : CoreIdent :=
  CoreIdent.unres (sanitizeIdent i.toString)

def varToCore (s : String) : CoreIdent :=
  CoreIdent.unres (sanitizeIdent s)

def envExtend (env : VarEnv) (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := env) fun acc (n, t) => acc.insert n t

def envFromDecls (decls : List (String × Typ)) : VarEnv :=
  envExtend Std.HashMap.emptyWithCapacity decls

def envFind? (env : VarEnv) (key : String) : Option Typ :=
  env.fold (fun acc k v => if k == key then some v else acc) none

def boundIndex? (bound : BoundEnv) (name : String) : Option Nat :=
  let rec go (i : Nat) (rest : BoundEnv) : Option Nat :=
    match rest with
    | [] => none
    | (n, _) :: tail => if n == name then some i else go (i + 1) tail
  go 0 bound

def boundType? (bound : BoundEnv) (name : String) : Option Typ :=
  match bound.find? (fun (n, _) => n == name) with
  | some (_, t) => some t
  | none => none

def listWithIndices (xs : List α) : List (α × Nat) :=
  let rec go (i : Nat) (rest : List α) : List (α × Nat) :=
    match rest with
    | [] => []
    | x :: xs' => (x, i) :: go (i + 1) xs'
  go 0 xs

def concatMap (f : α → List β) (xs : List α) : List β :=
  xs.foldl (init := []) (fun acc x => acc ++ f x)

def isFuelVar : Exp → Bool
  | .Var name => name.startsWith "fuel%" || name.startsWith "fuel_"
  | _ => false

/-! ## Type Translation -/

def monoTyOfTyp (ctx : ToCoreCtx) : Typ → LMonoTy
  | .Empty => .tcons "Unit" []
  | .Unit => .tcons "Unit" []
  | .Tuple t1 t2 => .tcons "Tuple" [monoTyOfTyp ctx t1, monoTyOfTyp ctx t2]
  | .Bool => .bool
  | .Int => .int
  | .Nat => .int
  -- map u32 to int for now
  | .UInt w => if ctx.useIntU32 && w == 32 then .int else .bitvec w
  | .SInt w => .bitvec w
  | .Char => .int -- TODO
  | .StrSlice => .string
  | .Array t => Core.mapTy .int (monoTyOfTyp ctx t)
  | .TypParam name => .ftvar name -- TODO
  | .SpecFn params ret =>
    let paramTys := params.map (monoTyOfTyp ctx)
    LMonoTy.mkArrow' (monoTyOfTyp ctx ret) paramTys
  | .Decorated _ ty => monoTyOfTyp ctx ty -- TODO, ignore for now
  | .Struct name params => .tcons (sanitizeIdent name.toString) (params.map (monoTyOfTyp ctx))
  | .Enum name params => .tcons (sanitizeIdent name.toString) (params.map (monoTyOfTyp ctx))
  | .AirNamed str => .tcons str []

def tyOfTyp (ctx : ToCoreCtx) (t : Typ) : LTy :=
  .forAll [] (monoTyOfTyp ctx t)

def needsReturn (t : Typ) : Bool :=
  match t with
  | .Unit | .Empty => false
  | _ => true

def bitWidthOfTyp (ctx : ToCoreCtx) : Typ → Option Nat
  | .UInt w => if ctx.useIntU32 && w == 32 then none else some w
  | .SInt w => some w
  | .Decorated _ ty => bitWidthOfTyp ctx ty
  | _ => none

/-! ## Expression Translation -/

def constToCore (ctx : ToCoreCtx) (expected? : Option Typ) : Const → CoreExpr
  | .Bool b => LExpr.boolConst () b
  | .Int i =>
    match expected?.bind (bitWidthOfTyp ctx) with
    | some w =>
      let n := Int.toNat i
      LExpr.bitvecConst () w (BitVec.ofNat w n)
    | none => LExpr.intConst () i
  | .StrSlice s => LExpr.strConst () s
  | .Char c => LExpr.intConst () c.toNat

def varExpr (ctx : ToCoreCtx) (env : VarEnv) (name : String) : CoreExpr :=
  let ty? := envFind? env name |>.map (monoTyOfTyp ctx)
  LExpr.fvar () (varToCore name) ty?

def applyOp (op : CoreExpr) (args : List CoreExpr) : CoreExpr :=
  LExpr.mkApp () op args

def binaryOpToCore : BinaryOp → Option CoreExpr
  | .And => some Core.boolAndOp
  | .Or => some Core.boolOrOp
  | .Implies => some Core.boolImpliesOp
  | .Eq _ => none
  | .Ne => none
  | .Xor => none
  | .Inequality .Le => some Core.intLeOp
  | .Inequality .Lt => some Core.intLtOp
  | .Inequality .Ge => some Core.intGeOp
  | .Inequality .Gt => some Core.intGtOp
  | .Arith .Add _ => some Core.intAddOp
  | .Arith .Sub _ => some Core.intSubOp
  | .Arith .Mul _ => some Core.intMulOp
  | .Arith .EuclideanDiv _ => some Core.intDivOp
  | .Arith .EuclideanMod _ => some Core.intModOp
  | .Bitwise _ _ => none

def unaryOpToCore : UnaryOp → Option CoreExpr
  | .Not => some Core.boolNotOp
  | _ => none

/-- Inline let-bindings since Core expressions are let-free. -/
partial def substExp (name : String) (rhs : Exp) : Exp → Exp
  | .Const c => .Const c
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
  | .Unary op e => .Unary op (substExp name rhs e)
  | .Binary op e1 e2 => .Binary op (substExp name rhs e1) (substExp name rhs e2)
  | .If c t f => .If (substExp name rhs c) (substExp name rhs t) (substExp name rhs f)
  | .Bind bind body =>
    match bind with
    | .Let v ty e =>
      let e' := substExp name rhs e
      if v == name then
        .Bind (.Let v ty e') body
      else
        .Bind (.Let v ty e') (substExp name rhs body)
    | .Quant q vars =>
      if vars.any (fun (v, _) => v == name) then
        .Bind (.Quant q vars) body
      else
        .Bind (.Quant q vars) (substExp name rhs body)
    | .Lambda vars =>
      if vars.any (fun (v, _) => v == name) then
        .Bind (.Lambda vars) body
      else
        .Bind (.Lambda vars) (substExp name rhs body)
  | .ArrayLiteral elems => .ArrayLiteral (elems.map (substExp name rhs))
  | .MatchBlock scrut body =>
    let (e, t) := scrut
    .MatchBlock (substExp name rhs e, t) (substExp name rhs body)

partial def expToCoreWithBound (ctx : ToCoreCtx) (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) :
    Exp → Except String CoreExpr
  | .Const c => return constToCore ctx expected? c
  | .Var x =>
    match boundIndex? bound x with
    | some idx => return LExpr.bvar () idx
    | none => return varExpr ctx env x
  | .StructCtor dt fields => do
    let ctor := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_ctor")) none
    let args ← fields.mapM (fun (_, e) => expToCoreWithBound ctx env bound none e)
    return applyOp ctor args
  | .EnumCtor dt variant data => do
    let ctor := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent variant)) none
    let args ← data.mapM (fun (_, e) => expToCoreWithBound ctx env bound none e)
    return applyOp ctor args
  | .TupleCtor _ _ => throw "TODO: tuple constructors"
  | .Binary (.Eq _) lhs rhs => do
    let l ← expToCoreWithBound ctx env bound none lhs
    let r ← expToCoreWithBound ctx env bound none rhs
    return LExpr.eq () l r
  | .Binary .Ne lhs rhs => do
    let l ← expToCoreWithBound ctx env bound none lhs
    let r ← expToCoreWithBound ctx env bound none rhs
    let eq := LExpr.eq () l r
    return applyOp Core.boolNotOp [eq]
  | .Binary .Xor lhs rhs => do
    let l ← expToCoreWithBound ctx env bound none lhs
    let r ← expToCoreWithBound ctx env bound none rhs
    let eq := applyOp Core.boolEquivOp [l, r]
    return applyOp Core.boolNotOp [eq]
  | .Binary op lhs rhs => do
    let l ← expToCoreWithBound ctx env bound none lhs
    let r ← expToCoreWithBound ctx env bound none rhs
    match op with
    | .Bitwise _ _ => throw "TODO: bitvector ops"
    | _ =>
      match binaryOpToCore op with
      | some bop => return applyOp bop [l, r]
      | none => throw s!"unsupported binary op: {repr op}"
  | .Unary op e => do
    let x ← expToCoreWithBound ctx env bound expected? e
    match op with
    | .Clip _ _ => return x
    | .Trigger => return x
    | .Proj dt _variant field =>
      let proj := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent field)) none
      return applyOp proj [x]
    | .IsVariant dt variant =>
      let isFn := LExpr.op () (CoreIdent.unres ("is_" ++ sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent variant)) none
      return applyOp isFn [x]
    | .Proj' _ _ => throw "TODO: tuple projections"
    | .BitNot _ => throw "TODO: bitvector ops"
    | _ =>
      match unaryOpToCore op with
      | some uop => return applyOp uop [x]
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToCoreWithBound ctx env bound (some .Bool) c
    let t' ← expToCoreWithBound ctx env bound expected? t
    let e' ← expToCoreWithBound ctx env bound expected? e
    return LExpr.ite () c' t' e'
  | .Call fn _typs args => do
    let fname := match fn with
      | .Fun name => name
    let f := LExpr.op () (identToCore fname) none
    let argsFiltered := args.filter (fun e => !isFuelVar e)
    let args' ← argsFiltered.mapM (expToCoreWithBound ctx env bound none)
    return applyOp f args'
  | .CallLambda body args => do
    let fnExpr ← expToCoreWithBound ctx env bound none body
    let args' ← args.mapM (expToCoreWithBound ctx env bound none)
    return applyOp fnExpr args'
  | .Bind bind body =>
    match bind with
    | .Let v _ty rhs =>
      let body' := substExp v rhs body
      expToCoreWithBound ctx env bound expected? body'
    | .Quant q vars => do
      let boundVars := vars.reverse ++ bound
      let bodyExpr ← expToCoreWithBound ctx env boundVars (some .Bool) body
      let qk := match q with
        | .Forall => Lambda.QuantifierKind.all
        | .Exists => Lambda.QuantifierKind.exist
      let wrap := fun (_v, ty) acc =>
        LExpr.quant () qk (some (monoTyOfTyp ctx ty)) (LExpr.noTrigger ()) acc
      return vars.foldr wrap bodyExpr
    | .Lambda _vars =>
      throw "lambda expressions are not supported in Core output yet"
  | .MatchBlock _scrut body =>
    expToCoreWithBound ctx env bound expected? body
  | .ArrayLiteral _ => throw "TODO: array literals"

partial def expToCore (ctx : ToCoreCtx) (env : VarEnv) (expected? : Option Typ) (e : Exp) :
    Except String CoreExpr :=
  expToCoreWithBound ctx env [] expected? e

/-! ## Statement Translation -/

def boolTrue : CoreExpr :=
  LExpr.boolConst () true

def mkAssert (label : String) (e : CoreExpr) : Core.Statement :=
  Core.Statement.assert label e

def mkAssume (label : String) (e : CoreExpr) : Core.Statement :=
  Core.Statement.assume label e

def mkGoto (label : String) : Core.Statement :=
  Imperative.Stmt.goto label

def mkBlock (label : String) (stms : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.block label stms

def mkIte (cond : CoreExpr) (thenStms elseStms : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.ite cond thenStms elseStms

def mkLoop (guard : CoreExpr) (measure : Option CoreExpr) (inv : Option CoreExpr)
    (body : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.loop guard measure inv body

def mkAnd (es : List CoreExpr) : CoreExpr :=
  match es with
  | [] => boolTrue
  | e :: rest => rest.foldl (init := e) (fun acc x => applyOp Core.boolAndOp [acc, x])

def loopInvariantToCore (ctx : ToCoreCtx) (env : VarEnv) (invs : List LoopInvariant) :
    Except String (Option CoreExpr) := do
  let invs' ← invs.mapM (fun inv => expToCore ctx env (some .Bool) inv.body)
  if invs'.isEmpty then
    return none
  else
    return some (mkAnd invs')

mutual
partial def stmToCore (ctx : ToCoreCtx) (env : VarEnv) (retVar? : Option (String × Typ)) :
    Stm → Except String (List Core.Statement)
  | .Call fn _typArgs args => do
    let args' ← args.mapM (expToCore ctx env none)
    return [Core.Statement.call [] (sanitizeIdent fn.toString) args']
  | .Assert exp => do
    match exp with
    | .Unary (.HasType _) _ => return []
    | _ =>
      let e ← expToCore ctx env (some .Bool) exp
      return [mkAssert "" e]
  | .AssertBitVector requires ensures => do
    let reqs ← requires.mapM (expToCore ctx env (some .Bool))
    let enss ← ensures.mapM (expToCore ctx env (some .Bool))
    let reqStms := reqs.map (mkAssert "bv_requires")
    let ensStms := enss.map (mkAssert "bv_ensures")
    return reqStms ++ ensStms
  | .AssertQuery body => stmToCore ctx env retVar? body
  | .AssertCompute exp => do
    let e ← expToCore ctx env (some .Bool) exp
    return [mkAssert "compute" e]
  | .AssertLean exp => do
    let e ← expToCore ctx env (some .Bool) exp
    return [mkAssert "lean" e]
  | .Assume exp => do
    let e ← expToCore ctx env (some .Bool) exp
    return [mkAssume "assume" e]
  | .Assign lhs lhsTy rhs lhsIsInit => do
    let rhs' ← expToCore ctx env (some lhsTy) rhs
    let name := varToCore lhs
    if lhsIsInit then
      return [Core.Statement.init name (tyOfTyp ctx lhsTy) rhs']
    else
      return [Core.Statement.set name rhs']
  | .DeadEnd stm =>
    stmToCore ctx env retVar? stm
  | .Return exp => do
    match exp, retVar? with
    | none, _ => return []
    | some (.EnumCtor _ "tuple%0" []), _ => return []
    | some (.TupleCtor 0 []), _ => return []
    | some (.StructCtor _ []), _ => return []
    | some e, some (retName, retTy) =>
      let rhs ← expToCore ctx env (some retTy) e
      return [Core.Statement.set (varToCore retName) rhs]
    | some _, none => return []
  | .BreakOrContinue label isBreak =>
    let target := match label with
      | some l => sanitizeIdent l
      | none => if isBreak then "break" else "continue"
    return [mkGoto target]
  | .If cond b1 b2 => do
    let c ← expToCore ctx env (some .Bool) cond
    let thenStms ← stmToCore ctx env retVar? b1
    let elseStms ← match b2 with
      | some s => stmToCore ctx env retVar? s
      | none => pure []
    return [mkIte c thenStms elseStms]
  | .Loop _isForLoop label cond body invs => do
    let condExpr ← match cond with
      | some (_, e) => expToCore ctx env (some .Bool) e
      | none => pure (boolTrue : CoreExpr)
    let condStms ← match cond with
      | some (s, _) => stmToCore ctx env retVar? s
      | none => pure []
    let invExpr? ← loopInvariantToCore ctx env invs
    let bodyStms ← stmToCore ctx env retVar? body
    let loopStmt := mkLoop condExpr none invExpr? bodyStms
    let stmt :=
      match label with
      | some l => mkBlock (sanitizeIdent l) [loopStmt]
      | none => loopStmt
    return condStms ++ [stmt]
  | .OpenInvariant stm =>
    stmToCore ctx env retVar? stm
  | .ClosureInner body =>
    stmToCore ctx env retVar? body
  | .Block stms =>
    stmListToCore ctx env retVar? stms

partial def stmListToCore (ctx : ToCoreCtx) (env : VarEnv) (retVar? : Option (String × Typ)) :
    List Stm → Except String (List Core.Statement)
  | .Assign lhs lhsTy rhs lhsIsInit :: .Assert (.Var v1) :: .Assume (.Var v2) :: rest =>
    if lhs == v1 && v1 == v2 then
      do
        let e ← expToCore ctx env (some lhsTy) rhs
        let st := mkAssert "" e
        let tail ← stmListToCore ctx env retVar? rest
        return st :: tail
    else
      do
        let s1 ← stmToCore ctx env retVar? (.Assign lhs lhsTy rhs lhsIsInit)
        let s2 ← stmToCore ctx env retVar? (.Assert (.Var v1))
        let s3 ← stmToCore ctx env retVar? (.Assume (.Var v2))
        let tail ← stmListToCore ctx env retVar? rest
        return s1 ++ s2 ++ s3 ++ tail
  | stm :: rest => do
    let s1 ← stmToCore ctx env retVar? stm
    let s2 ← stmListToCore ctx env retVar? rest
    return s1 ++ s2
  | [] => return []
end

/-! ## Local Variable Collection -/

mutual
partial def collectLocals : Stm → List (String × Typ)
  | .Assign lhs ty _rhs _isInit => [(lhs, ty)]
  | .AssertQuery body => collectLocals body
  | .DeadEnd stm => collectLocals stm
  | .If _cond b1 b2 =>
    collectLocals b1 ++ (b2.map collectLocals).getD []
  | .Loop _isForLoop _label cond body _invs =>
    let condLocals := match cond with
      | some (s, _) => collectLocals s
      | none => []
    condLocals ++ collectLocals body
  | .OpenInvariant stm => collectLocals stm
  | .ClosureInner body => collectLocals body
  | .Block stms => collectLocalsList stms
  | _ => []

partial def collectLocalsList : List Stm → List (String × Typ)
  | .Assign lhs ty rhs isInit :: .Assert (.Var v1) :: .Assume (.Var v2) :: rest =>
    if lhs == v1 && v1 == v2 then
      collectLocalsList rest
    else
      collectLocals (.Assign lhs ty rhs isInit)
        ++ collectLocalsList (.Assert (.Var v1) :: .Assume (.Var v2) :: rest)
  | stm :: rest => collectLocals stm ++ collectLocalsList rest
  | [] => []
end

def dedupLocals (locals : List (String × Typ)) : List (String × Typ) :=
  locals.foldl (init := []) (fun acc (n, t) =>
    if acc.any (fun (n', _) => n' == n) then acc else acc ++ [(n, t)])

def ctxFromDecls (_decls : List Decl) : ToCoreCtx :=
  -- TODO: compute context flags from decls (e.g. bitvector usage).
  { useIntU32 := true }

/-! ## Declaration Translation -/

def signatureOf (ctx : ToCoreCtx) (decls : List (String × Typ)) :
    @Lambda.LMonoTySignature Visibility :=
  decls.map (fun (n, t) => (varToCore n, monoTyOfTyp ctx t))

def mkChecks (ctx : ToCoreCtx) (env : VarEnv) (checkPrefix : String) (exps : List Exp) :
    Except String (ListMap CoreLabel Procedure.Check) := do
  let exprs ← exps.mapM (expToCore ctx env (some .Bool))
  let checks := (listWithIndices exprs).map (fun (e, idx) =>
    (s!"{checkPrefix}{idx}", { expr := e, attr := .Default }))
  return checks

def specFnToCore (ctx : ToCoreCtx) (emitBody : Bool) (f : SpecFn) : Except String Core.Function := do
  let env := envFromDecls f.inputs
  let body ←
    if emitBody then
      expToCore ctx env (some f.returnType) f.body
    else
      pure (boolTrue : CoreExpr)
  return {
    name := identToCore f.name
    typeArgs := []
    inputs := signatureOf ctx f.inputs
    output := monoTyOfTyp ctx f.returnType
    body := if emitBody then some body else none
  }

def proofFnToCore (ctx : ToCoreCtx) (f : ProofFn) : Except String Core.Procedure :=
  -- Placeholder: proof bodies are not emitted yet.
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf ctx f.inputs
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := []
      postconditions := []
    }
    body := []
  }

def execFnToCore (ctx : ToCoreCtx) (f : ExecFn) : Except String Core.Procedure := do
  let rawLocals := collectLocals f.body
  let hasRet := needsReturn f.returnType
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let env := envFromDecls (f.inputs ++ retDecls ++ dedupLocals rawLocals)
  let pre ← mkChecks ctx env "requires_" f.requires
  let post ← mkChecks ctx env "ensures_" f.ensures
  let retVar? := if hasRet then some (f.retName, f.returnType) else none
  let body ← stmToCore ctx env retVar? f.body
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf ctx f.inputs
      outputs := signatureOf ctx retDecls
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body := body
  }

def assertionToCore (ctx : ToCoreCtx) (a : Assertion) : Except String Core.Procedure :=
  -- Placeholder: assertion bodies are not emitted yet.
  return {
    header := {
      name := identToCore a.name
      typeArgs := []
      inputs := signatureOf ctx a.decls
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := []
      postconditions := []
    }
    body := []
  }

-- TODO
def funcCheckSstToCore (ctx : ToCoreCtx) (f : FuncCheckSst) : Except String Core.Procedure := do
  let env := envFromDecls f.decls
  let pre ← mkChecks ctx env "requires_" f.reqs
  let post ← mkChecks ctx env "ensures_" f.postCondition
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf ctx f.decls
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body := []
  }

-- TODO: struct/enum/tuple/array translations

partial def declToCore (ctx : ToCoreCtx) : Decl → Except String (List Core.Decl)
  | .assertion a => do
    let p ← assertionToCore ctx a
    return [Core.Decl.proc p]
  | .specFn f => do
    let fn ← specFnToCore ctx true f
    return [Core.Decl.func fn]
  | .proofFn f => do
    let p ← proofFnToCore ctx f
    return [Core.Decl.proc p]
  | .execFn f => do
    let p ← execFnToCore ctx f
    return [Core.Decl.proc p]
  | .func f => do
    let p ← funcCheckSstToCore ctx f
    return [Core.Decl.proc p]
  | .struct _ => throw "TODO: struct translation not implemented yet"
  | .enum _ => throw "TODO: enum translation not implemented yet"
  | .mutualBlock ds => do
    let parts ← ds.mapM (fun d =>
      match d with
      | .specFn f => do
        let fn ← specFnToCore ctx true f
        return [Core.Decl.func fn]
      | _ => declToCore ctx d)
    -- TODO: mutual recursion?
    return parts.flatten

def declsToProgram (decls : List Decl) : Except String Core.Program := do
  let ctx := ctxFromDecls decls
  let parts ← decls.mapM (declToCore ctx)
  let flat := parts.flatten
  let typeDecls := flat.filter (fun d => match d with | .type _ _ => true | _ => false)
  let otherDecls := flat.filter (fun d => match d with | .type _ _ => false | _ => true)
  -- TODO: add tuple/array/opaque-type preludes when those translations land.
  return { decls := typeDecls ++ otherDecls }


/-! ## Strata Core pretty-printer (temp) -/
namespace Pretty

mutual
partial def monoTyToString : LMonoTy → String
  | .tcons "bool" [] => "bool"
  | .tcons "int" [] => "int"
  | .tcons "string" [] => "string"
  | .bitvec n => s!"bv{n}"
  | .ftvar n => n
  | .tcons name [] => name
  | .tcons name args =>
    let argsStr := String.intercalate " " (args.map monoTyArgToString)
    s!"{name} {argsStr}"

partial def monoTyArgToString : LMonoTy → String
  | t@(.tcons _ (_ :: _)) => s!"({monoTyToString t})"
  | t => monoTyToString t
end

def tyToString (ty : LTy) : String :=
  match ty with
  | .forAll _ mty => monoTyToString mty

partial def exprToString (e : CoreExpr) : String :=
  exprToStringWithBound [] e
where
  constToString : LConst → String
  | .intConst i => toString i
  | .boolConst b => if b then "true" else "false"
  | .strConst s => s!"\"{s}\""
  | .realConst r => toString r
  | .bitvecConst n b => "bv{" ++ toString n ++ "}(" ++ toString b.toNat ++ ")"

  collectApps : CoreExpr → CoreExpr × List CoreExpr
  | .app _ fn arg =>
    let (h, args) := collectApps fn
    (h, args ++ [arg])
  | e => (e, [])

  callString (name : String) (args : List String) : String :=
    s!"{name}({String.intercalate ", " args})"

  bvUnaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "Not" => some "~"
      | some "Neg" => some "-"
      | _ => none
    else
      none

  bvBinaryOp? (name : String) : Option String :=
    if name.startsWith "Bv" then
      match (name.splitOn ".").getLast? with
      | some "And" => some "&"
      | some "Or" => some "|"
      | some "Xor" => some "^"
      | some "Shl" => some "<<"
      | some "UShr" => some ">>"
      | some "SShr" => some ">>s"
      | some "UDiv" => some "div"
      | some "UMod" => some "mod"
      | some "SDiv" => some "sdiv"
      | some "SMod" => some "smod"
      | some "ULt" => some "<"
      | some "ULe" => some "<="
      | some "UGt" => some ">"
      | some "UGe" => some ">="
      | some "SLt" => some "<s"
      | some "SLe" => some "<=s"
      | some "SGt" => some ">s"
      | some "SGe" => some ">=s"
      | _ => none
    else
      none

  getBound? (bound : List String) (idx : Nat) : Option String :=
    let rec go (i : Nat) (rest : List String) : Option String :=
      match rest with
      | [] => none
      | x :: xs => if i == idx then some x else go (i + 1) xs
    go 0 bound

  exprToStringWithBound (bound : List String) (e : CoreExpr) : String :=
    match e with
    | .const _ c => constToString c
    | .fvar _ id _ => CoreIdent.toPretty id
    | .op _ id _ => CoreIdent.toPretty id
    | .bvar _ idx =>
      match getBound? bound idx with
      | some name => name
      | none => s!"_b{idx}"
    | .eq _ a b => s!"({exprToStringWithBound bound a} == {exprToStringWithBound bound b})"
    | .ite _ c t f =>
      s!"(if {exprToStringWithBound bound c} then {exprToStringWithBound bound t} \
else {exprToStringWithBound bound f})"
    | .quant _ k ty _ body =>
      let name := s!"x{bound.length}"
      let kw := match k with
        | .all => "forall"
        | .exist => "exists"
      let tyStr := ty.map (fun mty => tyToString (.forAll [] mty))
      let head := match tyStr with
        | some ts => s!"{kw} {name}: {ts} :: "
        | none => s!"{kw} {name} :: "
      head ++ exprToStringWithBound (name :: bound) body
    | .app _ _ _ =>
      let (head, args) := collectApps e
      match head, args with
      | .op _ id _, [a] =>
        match CoreIdent.toPretty id with
        | "Bool.Not" => s!"(!{exprToStringWithBound bound a})"
        | "Int.Neg" => s!"(-{exprToStringWithBound bound a})"
        | op =>
          match bvUnaryOp? op with
          | some sym => s!"({sym}{exprToStringWithBound bound a})"
          | none => callString op [exprToStringWithBound bound a]
      | .op _ id _, [a, b] =>
        let op := CoreIdent.toPretty id
        let lhs := exprToStringWithBound bound a
        let rhs := exprToStringWithBound bound b
        match op with
        | "Int.Add" => s!"({lhs} + {rhs})"
        | "Int.Sub" => s!"({lhs} - {rhs})"
        | "Int.Mul" => s!"({lhs} * {rhs})"
        | "Int.Div" => s!"({lhs} div {rhs})"
        | "Int.Mod" => s!"({lhs} mod {rhs})"
        | "Int.Lt" => s!"({lhs} < {rhs})"
        | "Int.Le" => s!"({lhs} <= {rhs})"
        | "Int.Gt" => s!"({lhs} > {rhs})"
        | "Int.Ge" => s!"({lhs} >= {rhs})"
        | "Bool.And" => s!"({lhs} && {rhs})"
        | "Bool.Or" => s!"({lhs} || {rhs})"
        | "Bool.Implies" => s!"({lhs} ==> {rhs})"
        | "Bool.Equiv" => s!"({lhs} == {rhs})"
        | _ =>
          match bvBinaryOp? op with
          | some sym => s!"({lhs} {sym} {rhs})"
          | none => callString op [lhs, rhs]
      | .op _ id _, _ =>
        callString (CoreIdent.toPretty id) (args.map (exprToStringWithBound bound))
      | .fvar _ id _, _ =>
        callString (CoreIdent.toPretty id) (args.map (exprToStringWithBound bound))
      | .bvar _ _, _ =>
        callString (exprToStringWithBound bound head) (args.map (exprToStringWithBound bound))
      | _, _ =>
        toString (Std.format e)
    | _ => toString (Std.format e)

def indentString (n : Nat) : String :=
  String.ofList (List.replicate (n * 2) ' ')

mutual
partial def stmtsToLines (indent : Nat) (ss : List Core.Statement) : List String :=
  ss.foldl (init := []) (fun acc s => acc ++ stmtToLines indent s)

partial def stmtToLines (indent : Nat) (s : Core.Statement) : List String :=
  let pad := indentString indent
  match s with
  | .cmd (.cmd (.init name ty e _)) =>
    let n := CoreIdent.toPretty name
    [s!"{pad}var {n} : {tyToString ty};", s!"{pad}{n} := {exprToString e};"]
  | .cmd (.cmd (.set name e _)) =>
    [s!"{pad}{CoreIdent.toPretty name} := {exprToString e};"]
  | .cmd (.cmd (.havoc name _)) =>
    [s!"{pad}havoc {CoreIdent.toPretty name};"]
  | .cmd (.cmd (.assert label e _)) =>
    if label.isEmpty then
      [s!"{pad}assert {exprToString e};"]
    else
      [s!"{pad}assert [{label}]: {exprToString e};"]
  | .cmd (.cmd (.assume label e _)) =>
    if label.isEmpty then
      [s!"{pad}assume {exprToString e};"]
    else
      [s!"{pad}assume [{label}]: {exprToString e};"]
  | .cmd (.cmd (.cover label e _)) =>
    if label.isEmpty then
      [s!"{pad}cover {exprToString e};"]
    else
      [s!"{pad}cover [{label}]: {exprToString e};"]
  | .cmd (.call lhs pname args _) =>
    let lhsStr :=
      if lhs.isEmpty then ""
      else s!"{String.intercalate ", " (lhs.map CoreIdent.toPretty)} := "
    let argsStr := String.intercalate ", " (args.map exprToString)
    [s!"{pad}call {lhsStr}{pname}({argsStr});"]
  | .block _ ss _ =>
    let body := stmtsToLines (indent + 1) ss
    [pad ++ "{"] ++ body ++ [pad ++ "}"]
  | .ite cond t e _ =>
    let head := s!"{pad}if ({exprToString cond}) " ++ "{"
    let thenLines := stmtsToLines (indent + 1) t
    let elseLines := stmtsToLines (indent + 1) e
    [head] ++ thenLines ++ [pad ++ "} else {"] ++ elseLines ++ [pad ++ "}"]
  | .loop guard _ inv body _ =>
    let invLine :=
      match inv with
      | none => []
      | some i => [s!"{pad}  invariant ({exprToString i});"]
    let head := s!"{pad}while ({exprToString guard})"
    let bodyLines := stmtsToLines (indent + 1) body
    [head] ++ invLine ++ [pad ++ "{"] ++ bodyLines ++ [pad ++ "}"]
  | .goto lbl _ =>
    [s!"{pad}goto {lbl};"]
end

def typeArgsToString (args : List String) : String :=
  if args.isEmpty then "" else s!"<{String.intercalate ", " args}>"

def typeParamsToString (num : Nat) : String :=
  if num == 0 then
    ""
  else
    let names := (List.range num).map (fun i => s!"T{i}")
    let binds := names.map (fun n => s!"{n}: Type")
    s!" ({String.intercalate ", " binds})"

def procToString (p : Core.Procedure) : String :=
  let inputs := sigToString p.header.inputs
  let outputs := sigToString p.header.outputs
  let header :=
    s!"procedure {CoreIdent.toPretty p.header.name}{typeArgsToString p.header.typeArgs}({inputs}) returns ({outputs})"
  let specLines :=
    (p.spec.modifies.map (fun v => s!"  modifies {CoreIdent.toPretty v};"))
    ++ (p.spec.preconditions.map (fun (_, c) => s!"  requires ({exprToString c.expr});"))
    ++ (p.spec.postconditions.map (fun (_, c) => s!"  ensures ({exprToString c.expr});"))
  let specBlock :=
    if specLines.isEmpty then
      []
    else
      ["spec {"] ++ specLines ++ ["}"]
  let bodyLines := stmtsToLines 1 p.body
  let body := ["{"] ++ bodyLines ++ ["};"]
  String.intercalate "\n" ([header] ++ specBlock ++ body)
where
  sigToString (sig : @Lambda.LMonoTySignature Visibility) : String :=
    String.intercalate ", " (sig.map (fun (id, ty) =>
      s!"{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))

def funcToString (f : Core.Function) : String :=
  let inputs := String.intercalate ", " (f.inputs.map (fun (id, ty) =>
    s!"{CoreIdent.toPretty id}: {tyToString (.forAll [] ty)}"))
  let header := s!"function {CoreIdent.toPretty f.name}{typeArgsToString f.typeArgs}({inputs}): {tyToString (.forAll [] f.output)}"
  match f.body with
  | none => header ++ ";"
  | some body =>
    let bodyStr := exprToString body
    String.intercalate "\n" [header ++ " {", "  " ++ bodyStr, "}"]

def declToString (d : Core.Decl) : String :=
  match d with
  | .proc p _ => procToString p
  | .func f _ => funcToString f
  | .type t _ =>
    match t with
    | .con c => s!"type {c.name}{typeParamsToString c.numargs};"
    | .syn s => s!"type {s.name} := {tyToString (.forAll [] s.type)};"
    | .data _ => "type /*data*/;"
  | .ax a _ => s!"axiom {CoreIdent.toPretty a.name}: {exprToString a.e};"
  | .var name ty e _ => s!"var {CoreIdent.toPretty name} : {tyToString ty} := {exprToString e};"
  | .distinct lbl es _ =>
    let esStr := String.intercalate ", " (es.map exprToString)
    s!"distinct [{lbl}] {esStr};"

def programToString (p : Core.Program) : String :=
  let decls := p.decls.map declToString
  let body := String.intercalate "\n\n" decls
  if body.isEmpty then
    "program Core;\n"
  else
    "program Core;\n\n" ++ body ++ "\n"

end Pretty

def declsToCoreString (decls : List Decl) : Except String String := do
  let p ← declsToProgram decls
  return Pretty.programToString p

end ToCore

end VerusLean
