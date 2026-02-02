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

def declSentinelName : String := "__verus_decl__"

def declSentinel : CoreExpr :=
  LExpr.fvar () (CoreIdent.unres declSentinelName) none

def isDeclSentinel : CoreExpr → Bool
  | LExpr.fvar _ id _ => CoreIdent.toPretty id == declSentinelName
  | _ => false

def identToCore (i : Ident) : CoreIdent :=
  CoreIdent.unres (sanitizeIdent i.toString)

def varToCore (s : String) : CoreIdent :=
  CoreIdent.unres (sanitizeIdent s)

def envFromDecls (decls : List (String × Typ)) : VarEnv :=
  decls.foldl (init := Std.HashMap.emptyWithCapacity) fun acc (n, t) => acc.insert n t

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

def isFuelVar : Exp → Bool
  | .Var name => name.startsWith "fuel%" || name.startsWith "fuel_"
  | _ => false

/-! ## Type Translation -/

def monoTyOfTyp : Typ → LMonoTy
  | .Empty => .tcons "Unit" []
  | .Unit => .tcons "Unit" []
  | .Tuple t1 t2 => .tcons "Tuple" [monoTyOfTyp t1, monoTyOfTyp t2]
  | .Bool => .bool
  | .Int => .int
  | .Nat => .int
  | .UInt w => .bitvec w
  | .SInt w => .bitvec w
  | .Char => .int -- TODO
  | .StrSlice => .string
  | .Array t => Core.mapTy .int (monoTyOfTyp t)
  | .TypParam name => .ftvar name -- TODO
  | .SpecFn params ret =>
    let paramTys := params.map monoTyOfTyp
    LMonoTy.mkArrow' (monoTyOfTyp ret) paramTys
  | .Decorated _ ty => monoTyOfTyp ty -- TODO, ignore for now
  | .Struct name params => .tcons (sanitizeIdent name.toString) (params.map monoTyOfTyp)
  | .Enum name params => .tcons (sanitizeIdent name.toString) (params.map monoTyOfTyp)
  | .AirNamed str => .tcons str []

def bitWidthOfTyp : Typ → Option Nat
  | .UInt w => some w
  | .SInt w => some w
  | .Decorated _ ty => bitWidthOfTyp ty
  | _ => none

def bitInfoOfTyp : Typ → Option (Nat × Bool)
  | .UInt w => some (w, false)
  | .SInt w => some (w, true)
  | .Decorated _ ty => bitInfoOfTyp ty
  | _ => none

/-! ## Expression Translation -/

def constToCore (expected? : Option Typ) : Const → CoreExpr
  | .Bool b => LExpr.boolConst () b
  | .Int i =>
    match expected?.bind bitWidthOfTyp with
    | some w =>
      LExpr.bitvecConst () w (BitVec.ofInt w i)
    | none => LExpr.intConst () i
  | .StrSlice s => LExpr.strConst () s
  | .Char c => LExpr.intConst () c.toNat

def bvByWidth (w : Nat)
    (op1 op8 op16 op32 op64 : CoreExpr) : Option CoreExpr :=
  match w with
  | 1 => some op1
  | 8 => some op8
  | 16 => some op16
  | 32 => some op32
  | 64 => some op64
  | _ => none

def bvOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "And" => bvByWidth w Core.bv1AndOp Core.bv8AndOp Core.bv16AndOp Core.bv32AndOp Core.bv64AndOp
  | "Or" => bvByWidth w Core.bv1OrOp Core.bv8OrOp Core.bv16OrOp Core.bv32OrOp Core.bv64OrOp
  | "Xor" => bvByWidth w Core.bv1XorOp Core.bv8XorOp Core.bv16XorOp Core.bv32XorOp Core.bv64XorOp
  | "Shl" => bvByWidth w Core.bv1ShlOp Core.bv8ShlOp Core.bv16ShlOp Core.bv32ShlOp Core.bv64ShlOp
  | "UShr" => bvByWidth w Core.bv1UShrOp Core.bv8UShrOp Core.bv16UShrOp Core.bv32UShrOp Core.bv64UShrOp
  | "SShr" => bvByWidth w Core.bv1SShrOp Core.bv8SShrOp Core.bv16SShrOp Core.bv32SShrOp Core.bv64SShrOp
  | "Not" => bvByWidth w Core.bv1NotOp Core.bv8NotOp Core.bv16NotOp Core.bv32NotOp Core.bv64NotOp
  | _ => none

def bvArithOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "Add" => bvByWidth w Core.bv1AddOp Core.bv8AddOp Core.bv16AddOp Core.bv32AddOp Core.bv64AddOp
  | "Sub" => bvByWidth w Core.bv1SubOp Core.bv8SubOp Core.bv16SubOp Core.bv32SubOp Core.bv64SubOp
  | "Mul" => bvByWidth w Core.bv1MulOp Core.bv8MulOp Core.bv16MulOp Core.bv32MulOp Core.bv64MulOp
  | "UDiv" => bvByWidth w Core.bv1UDivOp Core.bv8UDivOp Core.bv16UDivOp Core.bv32UDivOp Core.bv64UDivOp
  | "UMod" => bvByWidth w Core.bv1UModOp Core.bv8UModOp Core.bv16UModOp Core.bv32UModOp Core.bv64UModOp
  | "SDiv" => bvByWidth w Core.bv1SDivOp Core.bv8SDivOp Core.bv16SDivOp Core.bv32SDivOp Core.bv64SDivOp
  | "SMod" => bvByWidth w Core.bv1SModOp Core.bv8SModOp Core.bv16SModOp Core.bv32SModOp Core.bv64SModOp
  | _ => none

def bvCmpOp (w : Nat) (op : String) : Option CoreExpr :=
  match op with
  | "ULt" => bvByWidth w Core.bv1ULtOp Core.bv8ULtOp Core.bv16ULtOp Core.bv32ULtOp Core.bv64ULtOp
  | "ULe" => bvByWidth w Core.bv1ULeOp Core.bv8ULeOp Core.bv16ULeOp Core.bv32ULeOp Core.bv64ULeOp
  | "UGt" => bvByWidth w Core.bv1UGtOp Core.bv8UGtOp Core.bv16UGtOp Core.bv32UGtOp Core.bv64UGtOp
  | "UGe" => bvByWidth w Core.bv1UGeOp Core.bv8UGeOp Core.bv16UGeOp Core.bv32UGeOp Core.bv64UGeOp
  | "SLt" => bvByWidth w Core.bv1SLtOp Core.bv8SLtOp Core.bv16SLtOp Core.bv32SLtOp Core.bv64SLtOp
  | "SLe" => bvByWidth w Core.bv1SLeOp Core.bv8SLeOp Core.bv16SLeOp Core.bv32SLeOp Core.bv64SLeOp
  | "SGt" => bvByWidth w Core.bv1SGtOp Core.bv8SGtOp Core.bv16SGtOp Core.bv32SGtOp Core.bv64SGtOp
  | "SGe" => bvByWidth w Core.bv1SGeOp Core.bv8SGeOp Core.bv16SGeOp Core.bv32SGeOp Core.bv64SGeOp
  | _ => none

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
  | .BitNot (some w) => bvOp w "Not"
  | _ => none

def inferBitInfo (env : VarEnv) (bound : BoundEnv) (e : Exp) : Option (Nat × Bool) :=
  match e with
  | .Var x =>
    (boundType? bound x <|> env.get? x) |>.bind bitInfoOfTyp
  | .Unary (.BitNot (some w)) _ => some (w, false)
  | .Unary (.Clip (.U w) _) _ => some (w.toNat, false)
  | .Unary (.Clip (.I w) _) _ => some (w.toNat, true)
  | .Binary (.Bitwise (.Shl w _) _) _ _ => some (w, false)
  | .Binary (.Bitwise (.Shr w) _) _ _ => some (w, false)
  | .Unary _ e => inferBitInfo env bound e
  | .Binary _ e1 e2 => inferBitInfo env bound e1 <|> inferBitInfo env bound e2
  | .If _ t f => inferBitInfo env bound t <|> inferBitInfo env bound f
  | _ => none

-- Inline let-bindings since Core expressions are let-free.
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

partial def expToCoreWithBound (env : VarEnv) (bound : BoundEnv)
    (expected? : Option Typ) :
    Exp → Except String CoreExpr
  | .Const c => return constToCore expected? c
  | .Var x =>
    match boundIndex? bound x with
    | some idx => return LExpr.bvar () idx
    | none =>
      let ty? := env.get? x |>.map monoTyOfTyp
      return LExpr.fvar () (varToCore x) ty?
  | .StructCtor dt fields => do
    let ctor := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_ctor")) none
    let args ← fields.mapM (fun (_, e) => expToCoreWithBound env bound none e)
    return LExpr.mkApp () ctor args
  | .EnumCtor dt variant data => do
    let ctor := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent variant)) none
    let args ← data.mapM (fun (_, e) => expToCoreWithBound env bound none e)
    return LExpr.mkApp () ctor args
  | .TupleCtor _ _ => throw "TODO: tuple constructors"
  | .Binary (.Eq _) lhs rhs => do
    let l ← expToCoreWithBound env bound none lhs
    let r ← expToCoreWithBound env bound none rhs
    return LExpr.eq () l r
  | .Binary .Ne lhs rhs => do
    let l ← expToCoreWithBound env bound none lhs
    let r ← expToCoreWithBound env bound none rhs
    let eq := LExpr.eq () l r
    return LExpr.mkApp () Core.boolNotOp [eq]
  | .Binary .Xor lhs rhs => do
    let info? := inferBitInfo env bound lhs <|> inferBitInfo env bound rhs
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    let l ← expToCoreWithBound env bound argTy? lhs
    let r ← expToCoreWithBound env bound argTy? rhs
    let eq := LExpr.mkApp () Core.boolEquivOp [l, r]
    return LExpr.mkApp () Core.boolNotOp [eq]
  | .Binary op lhs rhs => do
    let info? :=
      inferBitInfo env bound lhs
        <|> inferBitInfo env bound rhs
        <|> expected?.bind bitInfoOfTyp
    let argTy? := info?.map (fun (w, signed) => if signed then Typ.SInt w else Typ.UInt w)
    let l ← expToCoreWithBound env bound argTy? lhs
    let r ← expToCoreWithBound env bound argTy? rhs
    match op with
    | .Bitwise bitop _ =>
      let w? := match bitop with
        | .Shl w _ => some w
        | .Shr w => some w
        | _ => info?.map Prod.fst
      let signed := info?.map Prod.snd |>.getD false
      let opName := match bitop with
        | .BitAnd => "And"
        | .BitOr => "Or"
        | .BitXor => "Xor"
        | .Shl _ _ => "Shl"
        | .Shr _ => if signed then "SShr" else "UShr"
      match w? with
      | some w =>
        match bvOp w opName with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none => throw s!"missing bitvector width for op {opName}"
    | .Arith a _ =>
      match info? with
      | some (w, signed) =>
        let opName := match a with
          | .Add => "Add"
          | .Sub => "Sub"
          | .Mul => "Mul"
          | .EuclideanDiv => if signed then "SDiv" else "UDiv"
          | .EuclideanMod => if signed then "SMod" else "UMod"
        match bvArithOp w opName with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        match binaryOpToCore op with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported binary op: {repr op}"
    | .Inequality cmp =>
      match info? with
      | some (w, signed) =>
        let opName := match cmp with
          | .Le => if signed then "SLe" else "ULe"
          | .Lt => if signed then "SLt" else "ULt"
          | .Ge => if signed then "SGe" else "UGe"
          | .Gt => if signed then "SGt" else "UGt"
        match bvCmpOp w opName with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported bitvector width {w} for op {opName}"
      | none =>
        match binaryOpToCore op with
        | some bop => return LExpr.mkApp () bop [l, r]
        | none => throw s!"unsupported binary op: {repr op}"
    | _ =>
      match binaryOpToCore op with
      | some bop => return LExpr.mkApp () bop [l, r]
      | none => throw s!"unsupported binary op: {repr op}"
  | .Unary op e => do
    let x ← expToCoreWithBound env bound expected? e
    match op with
    | .Clip _ _ => return x
    | .Trigger => return x
    | .Box _ => return x
    | .Unbox _ => return x
    | .HasType _ => return x
    | .Proj dt _variant field =>
      let proj := LExpr.op () (CoreIdent.unres (sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent field)) none
      return LExpr.mkApp () proj [x]
    | .IsVariant dt variant =>
      let isFn := LExpr.op () (CoreIdent.unres ("is_" ++ sanitizeIdent dt.toString ++ "_" ++ sanitizeIdent variant)) none
      return LExpr.mkApp () isFn [x]
    | .Proj' _ _ => throw "TODO: tuple projections"
    | .BitNot none =>
      let w? :=
        (expected?.bind bitInfoOfTyp |>.map Prod.fst)
          <|> ((inferBitInfo env bound e).map Prod.fst)
      match w? with
      | some w =>
        match bvOp w "Not" with
        | some bop => return LExpr.mkApp () bop [x]
        | none => throw s!"unsupported bitvector width {w} for op Not"
      | none => throw "missing bitvector width for op Not"
    | _ =>
      match unaryOpToCore op with
      | some uop => return LExpr.mkApp () uop [x]
      | none => throw s!"unsupported unary op: {repr op}"
  | .If c t e => do
    let c' ← expToCoreWithBound env bound (some .Bool) c
    let t' ← expToCoreWithBound env bound expected? t
    let e' ← expToCoreWithBound env bound expected? e
    return LExpr.ite () c' t' e'
  | .Call fn _typs args => do
    let fname := match fn with
      | .Fun name => name
    let argsFiltered := args.filter (fun e => !isFuelVar e)
    let mkFallback := do
      let args' ← argsFiltered.mapM (expToCoreWithBound env bound none)
      let f := LExpr.op () (identToCore fname) none
      return LExpr.mkApp () f args'
    mkFallback
  | .CallLambda body args => do
    let fnExpr ← expToCoreWithBound env bound none body
    let args' ← args.mapM (expToCoreWithBound env bound none)
    return LExpr.mkApp () fnExpr args'
  | .Bind bind body =>
    match bind with
    | .Let v _ty rhs =>
      let body' := substExp v rhs body
      expToCoreWithBound env bound expected? body'
    | .Quant q vars => do
      let boundVars := vars.reverse ++ bound
      let bodyExpr ← expToCoreWithBound env boundVars (some .Bool) body
      let qk := match q with
        | .Forall => Lambda.QuantifierKind.all
        | .Exists => Lambda.QuantifierKind.exist
      let wrap := fun (_v, ty) acc =>
        LExpr.quant () qk (some (monoTyOfTyp ty)) (LExpr.noTrigger ()) acc
      return vars.foldr wrap bodyExpr
    | .Lambda _vars =>
      throw "TODO: lambda expressions"
  | .MatchBlock _scrut body =>
    expToCoreWithBound env bound expected? body
  | .ArrayLiteral _ => throw "TODO: array literals"

partial def expToCore (env : VarEnv) (expected? : Option Typ) (e : Exp) :
    Except String CoreExpr :=
  expToCoreWithBound env [] expected? e

/-! ## Statement Translation -/

def mkLoop (guard : CoreExpr) (measure : Option CoreExpr) (inv : Option CoreExpr)
    (body : List Core.Statement) : Core.Statement :=
  Imperative.Stmt.loop guard measure inv body

def loopInvariantToCore (env : VarEnv) (invs : List LoopInvariant) :
    Except String (Option CoreExpr) := do
  let invs' ← invs.mapM (fun inv => expToCore env (some .Bool) inv.body)
  if invs'.isEmpty then
    return none
  else
    let invExpr :=
      match invs' with
      | [] => LExpr.boolConst () true
      | e :: rest => rest.foldl (init := e) (fun acc x => LExpr.mkApp () Core.boolAndOp [acc, x])
    return some invExpr

mutual
partial def stmToCore (env : VarEnv) (retVar? : Option (String × Typ)) :
    Stm → Except String (List Core.Statement)
  | .Call fn _typArgs args => do
    let args' ← args.mapM (expToCore env none)
    return [Core.Statement.call [] (sanitizeIdent fn.toString) args']
  | .Assert exp => do
    match exp with
    | .Unary (.HasType _) _ => return []
    | _ =>
      let e ← expToCore env (some .Bool) exp
      return [Core.Statement.assert "" e]
  | .AssertBitVector requires ensures => do
    let reqs ← requires.mapM (expToCore env (some .Bool))
    let enss ← ensures.mapM (expToCore env (some .Bool))
    let reqStms := reqs.map (Core.Statement.assert "bv_requires") -- intended to be checked, placeholder
    let ensStms := enss.map (Core.Statement.assert "bv_ensures")
    return reqStms ++ ensStms
  | .AssertQuery body => stmToCore env retVar? body
  | .AssertCompute exp => do
    let e ← expToCore env (some .Bool) exp
    return [Core.Statement.assert "compute" e]
  | .AssertLean exp => do
    let e ← expToCore env (some .Bool) exp
    return [Core.Statement.assert "lean" e]
  | .Assume exp => do
    let e ← expToCore env (some .Bool) exp
    return [Core.Statement.assume "assume" e]
  | .Assign lhs lhsTy rhs lhsIsInit => do
    let rhs' ← expToCore env (some lhsTy) rhs
    let name := varToCore lhs
    if lhsIsInit then
      return [Core.Statement.init name (.forAll [] (monoTyOfTyp lhsTy)) rhs']
    else
      return [Core.Statement.set name rhs']
  | .DeadEnd stm =>
    stmToCore env retVar? stm
  | .Return exp => do
    match exp, retVar? with
    | none, _ => return []
    | some (.EnumCtor _ "tuple%0" []), _ => return []
    | some (.TupleCtor 0 []), _ => return []
    | some (.StructCtor _ []), _ => return []
    | some e, some (retName, retTy) =>
      let rhs ← expToCore env (some retTy) e
      return [Core.Statement.set (varToCore retName) rhs]
    | some _, none => return []
  | .BreakOrContinue label isBreak =>
    let target := match label with
      | some l => sanitizeIdent l
      | none => if isBreak then "break" else "continue"
    return [Imperative.Stmt.goto target]
  | .If cond b1 b2 => do
    let c ← expToCore env (some .Bool) cond
    let thenStms ← stmToCore env retVar? b1
    let elseStms ← match b2 with
      | some s => stmToCore env retVar? s
      | none => pure []
    return [Imperative.Stmt.ite c thenStms elseStms]
  | .Loop _isForLoop label cond body invs => do
    let condExpr ← match cond with
      | some (_, e) => expToCore env (some .Bool) e
      | none => pure (LExpr.boolConst () true : CoreExpr)
    let condStms ← match cond with
      | some (s, _) => stmToCore env retVar? s
      | none => pure []
    let invExpr? ← loopInvariantToCore env invs
    let bodyStms ← stmToCore env retVar? body
    let loopStmt := mkLoop condExpr none invExpr? bodyStms
    let stmt :=
      match label with
      | some l => Imperative.Stmt.block (sanitizeIdent l) [loopStmt]
      | none => loopStmt
    return condStms ++ [stmt]
  | .OpenInvariant stm =>
    stmToCore env retVar? stm
  | .ClosureInner body =>
    stmToCore env retVar? body
  | .Block stms =>
    stmListToCore env retVar? stms

partial def stmListToCore (env : VarEnv) (retVar? : Option (String × Typ)) :
    List Stm → Except String (List Core.Statement)
  | .Assign lhs lhsTy rhs lhsIsInit :: .Assert (.Var v1) :: .Assume (.Var v2) :: rest =>
    if lhs == v1 && v1 == v2 then
      do
        let e ← expToCore env (some lhsTy) rhs
        let st := Core.Statement.assert "" e
        let tail ← stmListToCore env retVar? rest
        return st :: tail
    else
      do
        let s1 ← stmToCore env retVar? (.Assign lhs lhsTy rhs lhsIsInit)
        let s2 ← stmToCore env retVar? (.Assert (.Var v1))
        let s3 ← stmToCore env retVar? (.Assume (.Var v2))
        let tail ← stmListToCore env retVar? rest
        return s1 ++ s2 ++ s3 ++ tail
  | stm :: rest => do
    let s1 ← stmToCore env retVar? stm
    let s2 ← stmListToCore env retVar? rest
    return s1 ++ s2
  | [] => return []
end

def dedupLocals (locals : List (String × Typ)) : List (String × Typ) :=
  locals.foldl (init := []) (fun acc (n, t) =>
    if acc.any (fun (n', _) => n' == n) then acc else acc ++ [(n, t)])

mutual
partial def collectInitVars : Stm → List String
  | .Assign lhs _ _ lhsIsInit => if lhsIsInit then [lhs] else []
  | .AssertQuery body => collectInitVars body
  | .DeadEnd stm => collectInitVars stm
  | .If _cond b1 b2 =>
    collectInitVars b1 ++ (b2.map collectInitVars).getD []
  | .Loop _isForLoop _label cond body _invs =>
    let condVars := match cond with
      | some (s, _) => collectInitVars s
      | none => []
    condVars ++ collectInitVars body
  | .OpenInvariant stm => collectInitVars stm
  | .ClosureInner body => collectInitVars body
  | .Block stms => collectInitVarsList stms
  | _ => []

partial def collectInitVarsList : List Stm → List String
  | stm :: rest => collectInitVars stm ++ collectInitVarsList rest
  | [] => []
end

/-! ## Declaration Translation -/

def signatureOf (decls : List (String × Typ)) :
    @Lambda.LMonoTySignature Visibility :=
  decls.map (fun (n, t) => (varToCore n, monoTyOfTyp t))

def mkChecks (env : VarEnv) (checkPrefix : String) (exps : List Exp) :
    Except String (ListMap CoreLabel Procedure.Check) := do
  let exprs ← exps.mapM (expToCore env (some .Bool))
  let rec withIdx (i : Nat) (rest : List CoreExpr) : ListMap CoreLabel Procedure.Check :=
    match rest with
    | [] => []
    | e :: es => (s!"{checkPrefix}{i}", { expr := e, attr := .Default }) :: withIdx (i + 1) es
  return withIdx 0 exprs

def specFnToCore (emitBody : Bool) (f : SpecFn) : Except String Core.Function := do
  let env := envFromDecls f.inputs
  let body ←
    if emitBody then
      expToCore env (some f.returnType) f.body
    else
      pure (LExpr.boolConst () true : CoreExpr)
  return {
    name := identToCore f.name
    typeArgs := []
    inputs := signatureOf f.inputs
    output := monoTyOfTyp f.returnType
    body := if emitBody then some body else none
  }

def proofFnToCore (f : ProofFn) : Except String Core.Procedure :=
  -- Placeholder: proof bodies are not emitted yet.
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf f.inputs
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := []
      postconditions := []
    }
    body := []
  }

def execFnToCore (f : ExecFn) : Except String Core.Procedure := do
  let hasRet :=
    match f.returnType with
    | .Unit | .Empty => false
    | _ => true
  let retDecls := if hasRet then [(f.retName, f.returnType)] else []
  let inputNames := f.inputs.map Prod.fst
  let retNames := if hasRet then [f.retName] else []
  let initVars := collectInitVars f.body
  let localsAll := dedupLocals <| f.locals.filter (fun (n, _) =>
    !(inputNames.any (fun x => x == n) || retNames.any (fun x => x == n)))
  let localsDecls := localsAll.filter (fun (n, _) => !initVars.any (fun x => x == n))
  let env := envFromDecls (f.inputs ++ retDecls ++ localsAll)
  let pre ← mkChecks env "requires_" f.requires
  let post ← mkChecks env "ensures_" f.ensures
  let retVar? := if hasRet then some (f.retName, f.returnType) else none
  let body ← stmToCore env retVar? f.body
  let localDecls :=
    localsDecls.map (fun (n, t) => Core.Statement.init (varToCore n) (.forAll [] (monoTyOfTyp t)) declSentinel)
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf f.inputs
      outputs := signatureOf retDecls
    }
    spec := {
      modifies := []
      preconditions := pre
      postconditions := post
    }
    body := localDecls ++ body
  }

def assertionToCore (a : Assertion) : Except String Core.Procedure :=
  -- Placeholder: assertion bodies are not emitted yet.
  return {
    header := {
      name := identToCore a.name
      typeArgs := []
      inputs := signatureOf a.decls
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
def funcCheckSstToCore (f : FuncCheckSst) : Except String Core.Procedure := do
  let env := envFromDecls f.decls
  let pre ← mkChecks env "requires_" f.reqs
  let post ← mkChecks env "ensures_" f.postCondition
  return {
    header := {
      name := identToCore f.name
      typeArgs := []
      inputs := signatureOf f.decls
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

partial def declToCore : Decl → Except String (List Core.Decl)
  | .assertion a => do
    let p ← assertionToCore a
    return [Core.Decl.proc p]
  | .specFn f => do
    let fn ← specFnToCore true f
    return [Core.Decl.func fn]
  | .proofFn f => do
    let p ← proofFnToCore f
    return [Core.Decl.proc p]
  | .execFn f => do
    let p ← execFnToCore f
    return [Core.Decl.proc p]
  | .func f => do
    let p ← funcCheckSstToCore f
    return [Core.Decl.proc p]
  | .struct _ => throw "TODO: struct translation not implemented yet"
  | .enum _ => throw "TODO: enum translation not implemented yet"
  | .mutualBlock ds => do
    let parts ← ds.mapM (fun d =>
      match d with
      | .specFn f => do
        let fn ← specFnToCore true f
        return [Core.Decl.func fn]
      | _ => declToCore d)
    -- TODO: mutual recursion?
    return parts.flatten

def declsToProgram (decls : List Decl) : Except String Core.Program := do
  let parts ← decls.mapM declToCore
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
      | some "Add" => some "+"
      | some "Sub" => some "-"
      | some "Mul" => some "*"
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
    if isDeclSentinel e then
      [s!"{pad}var {n} : {tyToString ty};"]
    else
      [s!"{pad}var {n} : {tyToString ty} := {exprToString e};"]
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
