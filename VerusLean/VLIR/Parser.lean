import VerusLean.Json
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Pp
import VerusLean.Basic.Monad
import VerusLean.Vstd.Seq.Defs
import VerusLean.Vstd.Set.Defs
import VerusLean.Vstd.Map.Defs
import Lean

namespace VerusLean

open Lean
open VName

/-- A map for variables. Alias for `Std.HashMap Ident Typ`. -/
abbrev VarMap := Std.HashMap String Typ

/-- A map for functions. Alias for `Std.HashMap Ident SpecFn`. -/
abbrev FnMap := Std.HashMap Ident SpecFn
abbrev DtMap := Std.HashMap Ident Struct
abbrev DeclMap := Std.HashMap Ident Decl

private def VstdStr := "Vstd"

/--
  The parsing monad for Verus JSONs,
  which includes a state with a map from variable names to types.

  All exceptions are strings.

  The state is a mapping from variable names to their (primitive) types.
  For example, an unsigned integer of width 32 (in Rust, a `u32`) would be `UInt 32`.

  TODO: handle shadowing
-/
structure ParserState where
  expectedType : Typ := .Bool
  freeVars : VarMap := {}
  locVars : VarMap := {}
  -- Acts like a stack?
  boundVars : List (String × Typ) := []
  defs : DeclMap := {}
  thms : DeclMap := {}
  defsInRevOrder : List Ident := []
  thmsInRevOrder : List Ident := []
deriving Inhabited, Repr

abbrev VParser := EStateM String ParserState

/-- Alias for `Except String`. The argument following `ExStr` is the return type. -/
abbrev ExStr := Except String

namespace VParser

open EStateM

def getTyp : VParser Typ :=
  do let st ← get; return st.expectedType

def setTyp (t : Typ) : VParser Unit :=
  modify fun st => { st with expectedType := t }

def getFreeVars : VParser VarMap :=
  do let st ← get; return st.freeVars

def setFreeVars (fvars : List (Ident × Typ)) : VParser Unit :=
  modify fun st => { st with freeVars := fvars.foldl (init := ∅) (fun acc ⟨i, t⟩ => acc.insert i t) }

def setFreeVars' (fvars : VarMap) : VParser Unit :=
  modify fun st => { st with freeVars := fvars }

def getLocVars : VParser VarMap :=
  do let st ← get; return st.locVars

def getBoundVars : VParser (List (String × Typ)) :=
  do let st ← get; return st.boundVars

-- Adds a free variable with the explicitly given name `var` and type `typ`.
def addFreeVarWithTyp (var : String) (typ : Typ) : VParser Unit := do
  modify fun st => { st with
    freeVars := st.freeVars.insert var typ
  }

def addLocVarWithTyp (var : String) (typ : Typ) : VParser Unit := do
  modify fun st => { st with
    locVars := st.locVars.insert var typ
  }

-- Adds a free variable, using the type stored in the state.
def addFreeVar (var : String) : VParser Unit := do
  addFreeVarWithTyp var (← getTyp)

def addLocVar (var : String) : VParser Unit := do
  addLocVarWithTyp var (← getTyp)

def pushBoundVar (var : String) (typ : Typ) : VParser Unit :=
  modify fun st => { st with boundVars := (var, typ) :: st.boundVars }

-- Pushes a list of bound vars.
-- Note that lower indexes in `vars` means they get popped off sooner.
-- This is opposite from what one might expect, but is typical stack behavior.
def pushBoundVars (vars : List (String × Typ)) : VParser Unit :=
  modify fun st => { st with boundVars := vars ++ st.boundVars }

-- Pops the newest bound variable off the stack.
-- If the stack is empty, nothing happens.
def popBoundVar : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.tail }

-- Pops the `n` newest bound variables off the stack.
-- If `n` is greater than the size of the stack, then the stack becomes empty.
def popBoundVars (n : Nat) : VParser Unit :=
  modify fun st => { st with boundVars := st.boundVars.drop n }

/-- Perform the state-ful function `fn` with the bound vars `vars`,
    then pops them off the bound variables stack before returning. -/
def withBoundVars (vars : List (String × Typ)) (fn : VParser α) : VParser α := do
  pushBoundVars vars
  let a ← fn
  popBoundVars vars.length
  return a

/--
  Run function `fn` and then pop any bound vars added under `fn`.

  Note that this assumes that `fn` will only add variables and not modify
  the ones already on the stack.
-/
def restoreCurrentBoundVarsAfter (fn : VParser α) : VParser α := do
  let n := List.length <| ← getBoundVars
  let a ← fn
  let m := List.length <| ← getBoundVars
  popBoundVars (m - n)
  return a

def restoreCurrentFreeVarsAfter (fn : VParser α) : VParser α := do
  let fvars ← getFreeVars
  setFreeVars []
  let a ← fn
  setFreeVars' fvars
  return a

/--
  Consults the bound vars, from newest to oldest, to see if one named `var` exists.
-/
def lookupBoundVarTyp? (var : String) : VParser (Option Typ) := do
  let boundVars ← getBoundVars
  match boundVars.find? (fun ⟨i, _⟩ => i == var) with
  | some (_, typ) => return some typ
  | none => return none

-- CC: TODO: addFreeVar if not bound? Marked `isMut`?

/--
  Only adds a free variable if it is not already bound locally.
-/
def addFreeVarWithTypIfNotBound (var : String) (typ : Typ) : VParser Unit := do
  match ← lookupBoundVarTyp? var with
  | some _ => return ()
  | none => addFreeVarWithTyp var typ

def addFreeVarIfNotBound (var : String) : VParser Unit := do
  addFreeVarWithTypIfNotBound var (← getTyp)

def addDecl (d : Decl) : VParser Unit :=
  match d with
  | .mutualBlock _ =>
    modify fun st =>
      let key := Lean.Name.str Lean.Name.anonymous s!"mutual_{st.defsInRevOrder.length}"
      { st with
        defs := st.defs.insert key d
        defsInRevOrder := key :: st.defsInRevOrder }
  | .assertion _
  | .proofFn _ => modify fun st => { st with
      thms := st.thms.insert (name d) d
      thmsInRevOrder := (name d) :: st.thmsInRevOrder }
  | _ => modify fun st => { st with
      defs := st.defs.insert (name d) d
      defsInRevOrder := (name d) :: st.defsInRevOrder }

-- TODO: Gets only from `defs`
def getDecl? (i : Ident) : VParser (Option Decl) :=
  do let st ← get; return st.defs.get? i

def getDefs : VParser (List Decl) := do
  let st ← get
  return st.defsInRevOrder.foldl (init := []) (fun acc i =>
    match st.defs.get? i with
    | some d => d :: acc
    | none => acc) -- TODO: remove this case, should never happen

def getThms : VParser (List Decl) := do
  let st ← get
  return st.thmsInRevOrder.foldl (init := []) (fun acc i =>
    match st.thms.get? i with
    | some d => d :: acc
    | none => acc) -- TODO: remove this case, should never happen

def coeWithState : Except String α → VParser α
  | .ok a => (fun s => Result.ok a s)
  | .error e => (fun s => Result.error e s)

instance instCoeExcept : Coe (Except String α) (VParser α) where
  coe := coeWithState

instance instCoeFunExcept {α : Type u} {β : Type} : Coe (α → ExStr β) (α → VParser β) where
  coe f := fun a => f a

end VParser

--------------------------------------------------------------------------------

open VParser

variable {m : Type → Type} [Monad m] [MonadExceptOf String m]

def xJsonFromSpanned (j : Json) : m Json :=
  j.getObjValM "x"

def widthFromJson (j : Json) : m Nat := do
  try
    j.getNatUnderKeyM "Width"
  catch _ => return 32 -- ArchWordSize, use 32 bit for now

def pathedNameFromJson (j : Json) (pathKey : String := "path") : m Ident := do
  let nameObj ← j.getObjValM pathKey
  let krate ← nameObj.getStrUnderKeyM "krate"
  let krate := String.capitalize krate
  let ident := Lean.Name.str .anonymous krate
  let isVstd := krate = VstdStr -- skip capitalized namespace if vstd
  let pathed ← nameObj.getArrUnderKeyM "segments"
  let name ← pathed.foldlM (init := ident) (fun acc i => do
    let name ← i.getStrM
    let nameCap := name.capitalize
    -- skip the middle capitalized name segment if we have a Vstd name
    if isVstd && (name = nameCap || name.contains '%') then
      return acc
    else
      return Lean.Name.str acc nameCap)

  -- De-capitalize most functions (unless it's `Vstd.X`)
  if isVstd && Ident.numSegments name ≤ 2 then
    return name
  else
    return Ident.mapTail String.decapitalize name

def pathedNameFromNameJson (j : Json) (nameKey : String := "name") (pathKey : String := "path") : m Ident := do
  let nameObj ← j.getObjValM nameKey
  pathedNameFromJson nameObj pathKey

/--
  Parse a type from an already-parsed type and a decoration.

  Verus defines the empty type `never` as a type decoration, and so to catch
  this, we parse `ty` already and return either `Empty` or a decorated type.
-/
def TypDecoration.fromJson (j : Json) (ty : Typ) : m Typ := do
  match ← j.getStrM with
  | "Never"    => return .Empty
  | "Ref"      => return .Decorated .Ref ty
  | "MutRef"   => return .Decorated .MutRef ty
  | "Box"      => return .Decorated .Box ty
  | "Rc"       => return .Decorated .Rc ty
  | "Arc"      => return .Decorated .Arc ty
  | "Ghost"    => return .Decorated .Ghost ty
  | "Tracked"  => return .Decorated .Tracked ty
  | "ConstPtr" => return .Decorated .ConstPtr ty
  | _ => throw s!"TypDecoration.fromJson: Expected one of \{ Never, Ref, MutRef, Box, Rc, Arc, Ghost, Tracked }, got {j}"

partial def Typ.fromJson (j : Json) : m Typ := do
  match j.getStr? with
  | .ok "Bool" => return .Bool
  | .ok _ => throw "unsupported primitive type"
  | .error _ =>
    match ← j["Primitive", "Int", "ConstInt", "Datatype", "Boxed", "Decorate", "Air", "Bool", "SpecFn", "TypParam"] with
    | ("Primitive", obj) =>
      let t ← obj.getArrM
      match t[0]? with
      | some j =>
        match j.getStr? with
        | .ok "StrSlice" => return .StrSlice
        | .ok "Array" =>
          -- In Verus, arrays are specified by their type and length
          -- We drop the length requirement (for now TODO)
          -- This type is in the first element of the array in the first index of `t`
          let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
          let ⟨arrTyp, _⟩ ← arr[1].getArrWithSizeGeM 2
          let typ ← Typ.fromJson arrTyp[0]
          return .Array typ
        | _ => throw s!"unsupported primitive type: {j}"
      | none => throw s!"error, json: {obj}"

    | ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => return .Int
      | .ok "Nat" => return .Nat
      | .ok "USize" => return .UInt 32 -- assume 32 bit for now
      | .ok _ => throw s!"unsupported Int object string: {obj}"
      | .error _ =>
        -- Now check if it is a fixed-width integer
        match obj.getFirstVal ["U", "I"] with
        | .error _ => throw s!"unsupported Int object: {obj}"
        | .ok ("U", obj) =>
          match obj.getNat? with
          | .ok width => return Typ.UInt width
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok ("I", obj) =>
          match obj.getNat? with
          | .ok width => return Typ.SInt width
          | .error e => throw s!"[Typ.fromJson?]: {e}"
        | .ok _ => throw s!"unsupported Int object: {obj}"

    | ("Datatype", obj) =>
      /-
        Filter the `Tuples` from the true datatypes.

        Verus represents tuples as Datatypes. The arity of the tuple is given
        after the colon. The elements in the array under index 1 are the type
        arguments to either the tuple or to the datatype.

        Because these aren't "Datatypes" on Lean's side of things, we direct
        any "Tuple" serialization to the correct type.
      -/
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
      match arr[0].getNatUnderKey? "Tuple" with
      | .ok arity =>
        match arity with
        | 0 => return .Unit
        | 1 => throw "Tuples should not have a single type"
        | a + 2 =>
          let ⟨typArray, _⟩ ← arr[1].getArrWithSizeGeM (a + 2)
          let typeParams ← typArray.mapM Typ.fromJson

          -- Fold from the right (because product is right-associative)
          match typeParams.foldr (init := none) (fun typ acc  =>
              match acc with
              | none => some typ
              | some acc => some <| .Tuple typ acc) with
          | none => throw "no type params"
          | some ty => return ty
      | .error _ =>
        let name ← pathedNameFromJson arr[0] "Path"
        let paramsArr ← arr[1].getArrM
        let params ← paramsArr.mapM Typ.fromJson
        return .Struct name params.toList

    -- Boxed types are mainly used for SMT encodings in Verus.
    -- In Lean, just take the base type.
    | ("Boxed", obj) => Typ.fromJson obj

    | ("Decorate", obj) =>
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
      let ty ← Typ.fromJson arr[2]
      TypDecoration.fromJson arr[0] ty

    | ("Air", obj) =>
      -- TODO: Remove these later?
      -- For now, assume all AIR types are named
      let name ← obj.getStrUnderKeyM "Named"
      return .AirNamed name

    | ("SpecFn", obj) =>
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let params ←
        match arr[0].getArr? with
        | .ok arr => arr.mapM Typ.fromJson
        | .error _ => throw s!"[Typ.fromJson?]: Expected an array of parameters, got {arr[0]}"
      let ret ← Typ.fromJson arr[1]
      return .SpecFn params.toList ret

    | ("TypParam", obj) => return .TypParam <| ← obj.getStrM

    | _ => throw "unsupported primitive type"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned {α : Type} (j : Json) (fj : Json → VParser α) : VParser α := do
  -- CC (4/15/25) some expressions are commands, and don't have types(?)
  match j.getObjVal? "typ" with
  | .ok typObj => setTyp <| ← Typ.fromJson typObj
  | _ => setTyp (← getTyp) -- no-op
  fj <| ← j.getObjVal? "x"

--------------------------------------------------------------------------------

def Mode.fromJson (j : Json) : m Mode := do
  match ← j.getStrM with
  | "Spec"  => return .Spec
  | "Proof" => return .Proof
  | "Exec"  => return .Exec
  | str => throw s!"[Mode.fromJson?]: Expected one of \{ Spec, Proof, Exec }, got {str}"

def IntRange.fromJson (j : Json) : m IntRange := do
  match j.getStr? with
  | .ok "Int" => return .Int
  | .ok "Nat" => return .Nat
  | .ok "USize" => return .USize
  | .ok "ISize" => return .ISize
  | .ok "Char" => return .Char
  | _ =>
    -- TODO: `U` and `I` cases
    match j.getFirstVal ["U", "I"] with
    | .error _ => throw s!"unsupported IntRange object: {j}"
    | .ok ("U", obj) =>
      match obj.getNat? with
      | .ok width => return .U (UInt32.ofNat width)
      | .error e => throw s!"[IntRange.fromJson?]: {e}"
    | .ok ("I", obj) =>
      match obj.getNat? with
      | .ok width => return .I (UInt32.ofNat width)
      | .error e => throw s!"[IntRange.fromJson?]: {e}"
    | _ => throw s!"[IntRange.fromJson?]: Expected one of \{ U, I }, got {j}"
    -- throw s!"Unexpected IntRange: {j}"

def Const.fromJson (j : Json) : m Const := do
  match ← j["Bool", "Int", "StrSlice", "Char"] with
  | ("Bool", v) => return Const.Bool <| ← v.getBoolM
  | ("Int", v) =>
    -- Ints are serialized as an array, with the first element the sign enum
    -- and the second value is the data, an array of u64s.
    let ⟨arr, _⟩ ← v.getArrWithSizeGeM 2
    let s := arr[0]
    let n := arr[1]
    match ← s.getNatM with
    | 0 =>
      -- no sign
      -- CZ: according to bigint.rs, 0 is minus, 1 is no sign, 2 is plus?
      return Const.Int 0
    | 1 =>
      -- positive number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArrM
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| Int.ofNat <| ← n.getNatM
    | 2 =>
      -- negative number
      -- TODO: Need some computation for the big int
      -- For now, take the first entry and move on
      let nArr ← n.getArrM
      let n := nArr.getD 0 (Json.num <| JsonNumber.fromNat 0)
      return Const.Int <| -(Int.ofNat <| ← n.getNatM)
    | _ => throw "[Const.fromJson?]: Expected an Int sign of 0, 1, or 2"
  | ("StrSlice", _) => throw "StrSlice not yet implemented"
  | ("Char", _) => throw "Char not yet implemented"
  | _ => throw "[Const.fromJson?]: Unexpected match"

def Bitwise.fromJson (j : Json) : m BitwiseOp :=
  match j.getStr? with
  | .ok "BitXor" => return .BitXor
  | .ok "BitAnd" => return .BitAnd
  | .ok "BitOr"  => return .BitOr
  | .ok str => throw s!"[Bitwise.fromJson?]: Expected one of \{ BitXor, BitAnd, BitOr }, got {str}"
  | .error _ => do
    -- Try one of the shifts instead
    -- They are Json objects that store the width (and sign extension)
    match ← j["Shr", "Shl"] with
    | ("Shr", obj) => do
      let width ← widthFromJson obj
      return .Shr width

    | ("Shl", obj) =>
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let width ← widthFromJson arr[0]
      return .Shl width (← arr[1].getBoolM)

    | _ => throw s!"[Bitwise.fromJson?]: Expected one of \{ Shr, Shl }, got {j}"

def ArithOp.fromJson (j : Json) : m ArithOp := do
  match ← j.getStrM with
  | "Add"          => return .Add
  | "Sub"          => return .Sub
  | "Mul"          => return .Mul
  | "EuclideanDiv" => return .EuclideanDiv
  | "EuclideanMod" => return .EuclideanMod
  | s => throw s!"[ArithOp.fromJson?]: Expected one of \{ Add, Sub, Mul, Div, Mod }, got {s}"

def InequalityOp.fromJson (j : Json) : m InequalityOp := do
  match ← j.getStrM with
  | "Le" => return .Le
  | "Ge" => return .Ge
  | "Lt" => return .Lt
  | "Gt" => return .Gt
  | s => throw s!"[InequalityOp.fromJson?]: Expected one of \{ Le, Ge, Lt, Gt }, got {s}"

def UnaryOp.fromJson (j : Json) : m UnaryOp := do
  match j.getStr? with
  | .ok "Not"    => return .Not
  | .ok "BitNot" => throw "BitNot not yet implemented"
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip }, got {s}"
  | .error _ =>
    match ← j["BitNot", "Trigger", "Clip"] with
    | ("BitNot", obj) => -- Try seeing if "BitNot" has a width
      let width ← widthFromJson obj
      return .BitNot width
    | ("Trigger", _) => return .Trigger
    | ("Clip", obj) =>
      let range ← IntRange.fromJson <| ← obj.getObjValM "range"
      let truncate ← obj.getBoolUnderKeyM "truncate"
      return .Clip range truncate
    | _ => throw s!"[UnaryOp.fromJson?]: Expected one of \{ BitNot, Trigger }, got {j}"

/--
  Parses a unary operation under the "UnaryOpr" key.

  Verus divides unary operations into simple and complex operations.
  Simple ones are generally logical or bitwise operations,
  and are parsed by `UnaryOp.fromJson?`.
  This function parses the complicated ones: projection, etc.

  -- TODO: Combine into `UnaryOp.fromJson?`?
  -- TODO: Require the parser state to refer to data types?
-/
def UnaryOp.oprFromJson (j : Json) : m UnaryOp := do
  match ← j["Field", "IsVariant", "Box", "Unbox", "HasType"] with
  | ("Field", obj) =>
    try
      let dt ← pathedNameFromJson (pathKey := "Path") <| ← obj.getObjValM "datatype"
      let variant ← obj.getStrUnderKeyM "variant"
      let field ← obj.getStrUnderKeyM "field"
      -- dbg_trace s!"[Elab.lean]: Proj: {dt} {variant} {field}"
      return .Proj dt variant field
    catch _ => -- see if it's a tuple
      try
        let dt ← obj.getObjValM "datatype"
        let size ← dt.getNatUnderKeyM "Tuple"
        let field := (← obj.getStrUnderKeyM "field").toNat!
        return .Proj' size field
      catch _ =>
        throw s!"[UnaryOp.oprFromJson?]: Encounter Field, neither Path nor Tuple is found, got {obj}"
  | ("IsVariant", obj) =>
    try
      let dt ← pathedNameFromJson (pathKey := "Path") <| ← obj.getObjValM "datatype"
      let variant ← obj.getStrUnderKeyM "variant"
      return .IsVariant dt variant
    catch _ => -- see if it's a tuple
      try
        let dt ← obj.getObjValM "datatype"
        let size ← dt.getNatUnderKeyM "Tuple"
        let field := match (← obj.getStrUnderKeyM "variant").splitOn.reverse with
          | x :: _ => x.toNat!
          | _ => 0
        return .Proj' size field
      catch _ =>
        throw s!"[UnaryOp.oprFromJson?]: Encounter IsVariant, neither Path nor Tuple is found, got {obj}"
  | ("Box", obj) =>
    let typ ← Typ.fromJson obj
    return .Box typ
  | ("Unbox", obj) =>
    let typ ← Typ.fromJson obj
    return .Unbox typ
  | ("HasType", obj) =>
    let typ ← Typ.fromJson obj
    return .HasType typ
  | _ => throw s!"unsupported unaryop: {j}"

def BinaryOp.fromJson (j : Json) : m BinaryOp :=
  -- Most are single strings, but some have other information attached
  match j.getStr? with
  | .ok "And"     => return .And
  | .ok "Or"      => return .Or
  | .ok "Xor"     => return .Xor
  | .ok "Implies" => return .Implies
  | .ok "Ne"      => return .Ne
  | .ok s => throw s!"[BinaryOp.fromJson?]: Expected one of \{ And, Or, Xor, Implies, Ne }, got {s}"
  | .error _ => do
    -- Try one of the object ops instead
    match ← j["Eq", "Inequality", "Bitwise", "Arith"] with
    | ("Eq", obj)         => return .Eq (← Mode.fromJson obj)
    | ("Inequality", obj) => return .Inequality (← InequalityOp.fromJson obj)
    | ("Bitwise", obj) =>
      -- Object under "Bitwise" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let op ← Bitwise.fromJson arr[0]
      let mode ← Mode.fromJson arr[1]
      return .Bitwise op mode
    | ("Arith", obj) =>
      -- Object under "Arith" should be a two-element array with an op and a mode
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let op ← ArithOp.fromJson arr[0]
      let mode ← Mode.fromJson arr[1]
      return .Arith op mode
    | _ => throw s!"unsupported binary op: {j}"

def Quant.fromJson (j : Json) : m Quant := do
  match ← j.getObjValM "quant" with
  | "Forall" => return .Forall
  | "Exists" => return .Exists
  | s => throw s!"[Quant.fromJson?]: Expected one of \{ Forall, Exists }, got {s}"

def CallFun.fromJson (j : Json) : m CallFun := do
  match ← j["Fun", "Recursive", "InternalFun"] with
  | ("Fun", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 1
    let name ← pathedNameFromJson arr[0]
    return .Fun name
  | ("Recursive", obj) =>
    let name ← pathedNameFromJson obj
    return .Fun name
  | ("InternalFun", obj) =>
    return .Fun <| String.toName <| ← obj.getStrM
  | s => throw s!"unexpected {s}"

def VarBinder.fromJson (j : Json) (key : String := "typ") : m (String × Typ) := do
  -- The parameter's name is the 0th index (the "VirParam" is the 1st index)
  let ⟨arr, _⟩ ← j.getArrUnderKeyWithSizeGeM "name" 1
  let name ← arr[0].getStrM
  let typ ← Typ.fromJson <| ← j.getObjValM key
  return (name, typ)

def VarBinder.typBindersFromJson (j : Json) : m (List (String × Typ)) := do
  let (arr : _root_.Array Json) ← j.getArrM
  arr.toList.mapM (VarBinder.fromJson · "a")

def Var.fromJson (j : Json) : m String := do
  let ⟨arr, _⟩ ← j.getArrWithSizeGeM 2
  let ident ← arr[0].getStrM
  match ident with
  | "tmp%" => return s!"tmp{← arr[1].getNatUnderKeyM "VirTemp"}"
  | _ => return ident


mutual /- {Bind, Exp}.fromJson -/

partial def Bind.fromJson (j : Json) : VParser Bind := do
  let obj ← xJsonFromSpanned j
  match ← obj["Quant", "Let", "Lambda", "Choose"] with
  | ("Quant", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 4
    let q ← Quant.fromJson arr[0]
    let binders ← VarBinder.typBindersFromJson arr[1]
    return .Quant q binders
  | ("Let", obj) =>
    /-
      The type of the expression is hidden in the `SpannedTyped<ExpX>`,
      so we need to parse the type carefully/separately.
    -/
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 1
    let binders ← arr.mapM (fun v => do
      let ⟨nameArr, _⟩ ← v.getArrUnderKeyWithSizeGeM "name" 1
      let name ← nameArr[0].getStrM
      let expObj ← v.getObjValM "a"
      -- Get the type manually
      let typ ← Typ.fromJson <| ← expObj.getObjValM "typ"
      let exp ← fromJsonSpanned expObj Exp.fromJson
      return (name, typ, exp))
    -- TODO: Expand `Let` to include any number. For now, assume only 1
    if hb : binders.size ≥ 1 then
      let (name, typ, exp) := binders[0]
      if binders.size > 1 then
        dbg_trace "TODO: expand Let to include any number of binders, got {binders}"
      return .Let name typ exp
    else
      throw s!"Expected at least one binder"

  | ("Lambda", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let binders ← VarBinder.typBindersFromJson arr[0]
    return .Lambda binders
    -- throw "not yet implemented Bind.Lambda"

  | ("Choose", _) => throw "not yet implemented Bind.Choose"

  | s => throw s!"unexpected: {s}"

partial def Exp.fromJson (j : Json) : VParser Exp := do
  -- Expect that exactly one of the enumerated options will be true
  match ← j["Const", "Var", "VarLoc", "Call", "CallLambda", "Ctor", "Unary", "UnaryOpr", "Binary", "BinaryOpr", "If", "Bind", "ArrayLiteral", "MatchBlock"] with
  | ("Const", obj) =>
    return .Const <| ← Const.fromJson obj

  | ("Var", obj) =>
    let ident ← Var.fromJson obj
    addFreeVarIfNotBound ident
    return .Var ident

  | ("VarLoc", obj) =>
    let ident ← Var.fromJson obj
    addLocVar ident
    return .Var ident

  | ("Call", obj) =>
    -- Should be an object with a function name and arguments
    -- The function's name is the 0th element, the arguments the 2nd element (an array)
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let callFn ← CallFun.fromJson arr[0]
    let expsJson ← arr[2].getArrM
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned · Exp.fromJson)
    return .Call callFn [] exps.toList

  | ("CallLambda", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let body ← fromJsonSpanned arr[0] Exp.fromJson
    let expsJson ← arr[1].getArrM
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned · Exp.fromJson)
    return .CallLambda body exps.toList

  | ("Ctor", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let mut dt : Ident := (.str .anonymous "")
    -- let mut variant := ""
    try
      dt ← pathedNameFromJson arr[0] "Path" -- if this fails, see if it is a tuple
      let variant ← arr[1].getStrM

      -- According to Verus, the order of the fields within a `Ctor` node
      -- is unspecified, so parsing should not rely on field order.
      let fields ← arr[2].getArrM

      -- For each field, parse a field name and its expression
      let parsedFields ← fields.mapM (fun fObj => do
        let name ← Json.getStrUnderKeyM fObj "name"
        -- The expression lies under two `Spanned` objects
        let a ← Json.getObjValM fObj "a"
        let exp ← fromJsonSpanned a Exp.fromJson
        return (name, exp))

      match ← getDecl? dt with
      | none => throw s!"[ExpX.fromJson]: Could not find datatype {dt}"
      | some (Decl.struct _) => return .StructCtor dt parsedFields.toList
      | some (Decl.enum _) => return .EnumCtor dt variant parsedFields.toList
      | _ => throw s!"[ExpX.fromJson]: Encountered an unexpected decl with name {dt}"

    catch e =>
      let size ← (← arr[0].getObjValM "Tuple") |>.getNatM
      let items ← arr[2].getArrM
      let parsedItems ← items.mapM (fun fObj => do
        let a ← Json.getObjValM fObj "a"
        let exp ← fromJsonSpanned a Exp.fromJson
        return exp)
      return .TupleCtor size parsedItems.toList -- TODO: handle tuples properly

  | ("Unary", obj) =>
    -- A unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let op   ← UnaryOp.fromJson arr[0]
    let data ← fromJsonSpanned arr[1] Exp.fromJson
    return .Unary op data

  | ("UnaryOpr", obj) =>
    -- A complex unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    -- dbg_trace s!"UnaryOpr arr: {arr}"
    let op  ← UnaryOp.oprFromJson arr[0]
    -- dbg_trace s!"UnaryOpr op: {op}"
    let data ← fromJsonSpanned arr[1] Exp.fromJson

    -- Erase (Un)Box operations, just return the base type or expression
    -- dbg_trace s!"UnaryOpr data: {data}"
    match op with
    | .Box _ | .Unbox _ => return data
    | _ => return .Unary op data

  | ("Binary", obj) =>
    -- A binary object should be an array with an op and two data elements
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let op    ← BinaryOp.fromJson arr[0]
    let data₁ ← fromJsonSpanned arr[1] Exp.fromJson
    let data₂ ← fromJsonSpanned arr[2] Exp.fromJson
    return .Binary op data₁ data₂

  | ("BinaryOpr", obj) =>
    throw "BinaryOpr not yet implemented"

  | ("If", obj) =>
    -- Should be an array with three expressions
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let cond    ← fromJsonSpanned arr[0] Exp.fromJson
    let branch₁ ← fromJsonSpanned arr[1] Exp.fromJson
    let branch₂ ← fromJsonSpanned arr[2] Exp.fromJson
    return .If cond branch₁ branch₂

  | ("Bind", obj) =>
    -- Should be an array with a bind and an expression
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let bind ← Bind.fromJson arr[0]
    let exp ← withBoundVars bind.idents (fromJsonSpanned arr[1] Exp.fromJson)
    return .Bind bind exp

  | ("ArrayLiteral", obj) =>
    -- `obj` should be an array with the exact elements
    let arr ← obj.getArrM
    let elems ← arr.mapM (fromJsonSpanned · Exp.fromJson)
    return .ArrayLiteral elems.toList

  | ("MatchBlock", obj) =>
    let scrutineeObj ← obj.getObjValM "scrutinee"
    let scrutinee ← fromJsonSpanned scrutineeObj Exp.fromJson
    let typ ← Typ.fromJson <| ← scrutineeObj.getObjValM "typ"
    -- dbg_trace s!"MatchBlock scrutinee: {scrutinee}, type: {typ}"
    let bodyObj ← obj.getObjValM "body"
    -- dbg_trace s!"MatchBlock bodyObj"
    -- let variant ← bodyObj.getStrUnderKeyM "variant"
    let body ← fromJsonSpanned bodyObj Exp.fromJson
    -- dbg_trace s!"MatchBlock body: {body}"
    return .MatchBlock (scrutinee, typ) body

  | s => throw s!"[ExpX.fromJson?]: Expected an Exp branch string, got {s}"

end /- mutual -/


/--
  Parses a `Dest` expression, but with the expectation that the result
  is an identifier. Mainly used to build `Assign`s.

  In Verus, there are several ways to store a variable identifier in an
  expression (an `Exp`): `Var`, `VarLoc`, `VarAt`, `Loc`, etc.

  This function will parse the underlying `Exp` under the "dest", but
  will throw an error if the expression is not a variable identifier.

  TODO: Dropped type information?
-/
def Dest.fromJson (j : Json) : VParser (String × Typ) := do
  let e ← fromJsonSpanned j Exp.fromJson
  let ty ← getTyp
  match e with
  | .Var i => return (i, ty)
  | _ => throw s!"Expected a variable expression, got {e}"

def LoopInvariant.fromJson (j : Json) : VParser LoopInvariant := do
  let atEntry ← j.getBoolUnderKeyM "at_entry"
  let atExit ← j.getBoolUnderKeyM "at_exit"
  let invObj ← j.getObjValM "inv"
  let invExp ← fromJsonSpanned invObj Exp.fromJson
  return LoopInvariant.mk atEntry atExit invExp


partial def Stm.fromJson (j : Json) : VParser Stm := do
  match ← j["Call", "Assert", "AssertBitVector", "AssertQuery", "AssertCompute", "AssertLean",
    "Assume", "Assign", "DeadEnd", "Return", "BreakOrContinue", "If", "Loop",
    "OpenInvariant", "ClosureInner", "Block", "Fuel", "RevealString", "Air"] with

  | ("Call", obj) =>
    let fnName ← pathedNameFromNameJson obj (nameKey := "fun")
    let typArgsArr ← obj.getArrUnderKeyM "typ_args"
    let typArgs ← typArgsArr.mapM (fromJsonSpanned · Typ.fromJson)
    let argsArr ← obj.getArrUnderKeyM "args"
    let args ← argsArr.mapM (fromJsonSpanned · Exp.fromJson)
    return .Call fnName typArgs.toList args.toList

  | ("Assert", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let e ← fromJsonSpanned arr[2] Exp.fromJson
    return .Assert e

  | ("AssertBitVector", obj) =>
    -- CC TODO: Untested. I haven't looked at an actual JSON yet to see if this matches
    let arrReq ← obj.getArrUnderKeyM "requires"
    let requires ← arrReq.mapM (fromJsonSpanned · Exp.fromJson)
    let arrEns ← obj.getArrUnderKeyM "ensures"
    let ensures ← arrEns.mapM (fromJsonSpanned · Exp.fromJson)
    return .AssertBitVector requires.toList ensures.toList

  | ("AssertQuery", obj) =>
    let bodyObj ← obj.getObjValM "body"
    let stm ← fromJsonSpanned bodyObj Stm.fromJson
    return .AssertQuery stm

  | ("AssertCompute", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .AssertCompute e

  | ("AssertLean", obj) =>
    let bodyObj ← obj.getObjValM "body"
    let e ← fromJsonSpanned bodyObj Exp.fromJson
    return .AssertLean e

  | ("Assume", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .Assume e

  | ("Assign", obj) =>
    -- CC TODO? Dropped type information? Parse RHS first?
    let lhsObj ← obj.getObjValM "lhs"
    let (lhs, lhsTy) ← Dest.fromJson <| ← lhsObj.getObjValM "dest"
    let lhsIsInit ← lhsObj.getBoolUnderKeyM "is_init"
    let rhsObj ← obj.getObjValM "rhs"
    let rhs ← fromJsonSpanned rhsObj Exp.fromJson
    return .Assign lhs lhsTy rhs lhsIsInit

  | ("DeadEnd", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .DeadEnd stm

  | ("Return", obj) =>
    match obj.getObjVal? "ret_exp" with
    | .ok retExpObj =>
      let retExp ← fromJsonSpanned retExpObj Exp.fromJson
      return .Return (some retExp)
    | .error _ => return .Return none

  | ("BreakOrContinue", obj) =>
    let isBreak ← obj.getBoolUnderKeyM "is_break"
    let label ←
      match obj.getObjVal? "label" with
      | .ok (.str s) => pure (some s)
      | .ok .null => pure none
      | .ok v => throw s!"expected string or null for label, got {v}"
      | .error _ => pure none
    return .BreakOrContinue label isBreak

  | ("If", obj) =>
    -- The three parts of an if-statement are stored in a Verus tuple
    -- So this should be an array of three elements
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let cond ← fromJsonSpanned arr[0] Exp.fromJson
    let branch₁ ← fromJsonSpanned arr[1] Stm.fromJson

    -- If the option in Verus is `Some`, it's an object; otherwise, it's `null`
    match arr[2] with
    | .null => return .If cond branch₁ none
    | x =>
      let branch₂ ← fromJsonSpanned x Stm.fromJson
      return .If cond branch₁ (some branch₂)

  | ("Loop", obj) =>
    let isForLoop ← obj.getBoolUnderKeyM "is_for_loop"
    let label ←
      match obj.getObjVal? "label" with
      | .ok (.str s) => pure (some s)
      | .ok .null => pure none
      | .ok v => throw s!"expected string or null for loop label, got {v}"
      | .error _ => pure none
    let cond ←
      match obj.getObjVal? "cond" with
      | .ok .null => pure none
      | .ok v => do
        let arr ← v.getArrM
        if h : arr.size ≥ 2 then
          let stm ← fromJsonSpanned arr[0] Stm.fromJson
          let exp ← fromJsonSpanned arr[1] Exp.fromJson
          pure (some (stm, exp))
        else
          throw s!"expected loop cond array of size 2, got {arr.size}"
      | .error _ => pure none
    let body ← fromJsonSpanned (← obj.getObjValM "body") Stm.fromJson
    let invsArr ← obj.getArrUnderKeyM "invs"
    let invs ← invsArr.mapM LoopInvariant.fromJson
    return .Loop isForLoop label cond body invs.toList

  | ("OpenInvariant", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .OpenInvariant stm

  | ("ClosureInner", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .ClosureInner stm

  | ("Block", obj) =>
    -- We enforce that the block has at least one statement
    let arr ← obj.getArrM
    let stmts ← arr.mapM (do Stm.fromJson <| ← xJsonFromSpanned ·)
    return .Block stmts.toList

  | ("Fuel", _) =>
    return .Block []

  | ("RevealString", _) =>
    return .Block []

  | ("Air", _) =>
    return .Block []

  | s => throw s!"[Stm.fromJson?]: Expected one of many Stm options, got {s}"


--------------------------------------------------------------------------------

def Assertion.fromJson (j : Json) : VParser Assertion := do
  let parentFunName ← pathedNameFromNameJson j (nameKey := "ParentFn")
  -- let assertionId ← j.getNatUnderKeyM "AssertId"
  let givenName ← j.getStrUnderKeyM "Name"
  let (_, parentFunName) := Ident.uncons parentFunName
  let parentFunName := Ident.mapTail (· ++ s!"_assert_{givenName}") parentFunName

  let body ← xJsonFromSpanned j
  let (exp, params) ← restoreCurrentFreeVarsAfter <| do
    let exp ← fromJsonSpanned body Exp.fromJson
    let params ← getFreeVars
    return (exp, params.toList)
  return Assertion.mk parentFunName params exp


def fnParseArgs (j : Json) : VParser (List (String × Typ)) := do
  let varsJson ← j.getArrUnderKeyM "pars"

  /-
    For whatever reason, Verus decides to serialize empty parameter lists
    with a single element with the name `["no%param", "AirLocal"]`.
    We filter out those (or rather, that one) parameters here.
  -/
  let varsJson := varsJson.filter (fun obj =>
    match obj.getArrByPath? ["x", "name"] with
    | .ok arr =>
      if h : arr.size > 0 then
        match arr[0].getStr? with
        | .ok name => name != "no%param"
        | _ => true
      else
        false
    | _ => true)

  let vars ← restoreCurrentBoundVarsAfter <| varsJson.mapM (fun v => do
    let ⟨i, ty⟩ ← VarBinder.fromJson <| ← xJsonFromSpanned v
    -- We build up the bound variables as we go (in case of dependent typing)
    pushBoundVar i ty
    return (i, ty))
  return vars.toList


def SpecFn.fromJson (j : Json) : VParser (Option SpecFn) := do
  let name ← pathedNameFromNameJson j
  if name.head = VstdStr then return none else
  let args ← fnParseArgs j

  -- TODO: This ignores other info about the return value, (a `Par` in Verus)
  let returnType ← Typ.fromJson <| ← j.getObjValByPathM ["ret", "x", "typ"]
  setTyp returnType

  -- Parse the body as an expression
  -- For spec functions, this expression is stored in the axioms
  let bodyObj ← j.getObjValByPath ["axioms", "spec_axioms", "body_exp"]
  let bodyExp ← fromJsonSpanned bodyObj Exp.fromJson

  try
    -- let termCheckKind ← j.getObjValByPathM ["axioms", "spec_axioms", "termination_check", "post_condition", "kind"]
    -- if termCheckKind != "DecreasesImplicitLemma" then
    let termCheck : Json ← j.getObjValByPath ["axioms", "spec_axioms", "termination_check"]
    let decreases ← fromJsonSpanned (← termCheck.getObjValM "body") Stm.fromJson
    return some <| SpecFn.mk name args returnType decreases bodyExp
  catch _ =>
    return some <| SpecFn.mk name args returnType none bodyExp


def ProofFn.fromJson (j : Json) : VParser ProofFn := do
  let name ← pathedNameFromNameJson j
  let args ← fnParseArgs j

  let requiresObj ← j.getArrByPathM ["exec_proof_check", "reqs"]
  let requires ← requiresObj.mapM (fromJsonSpanned · Exp.fromJson)

  -- TODO: This ignores other postcondition information
  let ensuresObj ← j.getArrByPathM ["exec_proof_check", "post_condition", "ens_exps"]
  let ensures ← ensuresObj.mapM (fromJsonSpanned · Exp.fromJson)

  -- CC TODO: Still need to examine the internals for `by (lean)`
  -- If the proof function is NOT marked `by (lean)`, then we don't need to
  -- store its proof body (Verus already proved it)
  --let isLean ← j.getBoolUnderPathM ["attrs", "lean"]
  --if isLean then
  -- Parse the body as an expression
  -- For proof functions, this expression is stored in the "exec_proof_check"
  let bodyObj ← j.getObjValByPathM ["exec_proof_check", "body", "x"]
  let bodyStm ← Stm.fromJson bodyObj
  return ProofFn.mk name args requires.toList ensures.toList bodyStm
  --else
    --return ProofFn.mk name args requires.toList ensures.toList none


def ExecFn.fromJson (j : Json) : VParser (Option ExecFn) := do
  let name ← pathedNameFromNameJson j
  if name.head = VstdStr then return none else
  let args ← fnParseArgs j
  let retBinder ← VarBinder.fromJson <| ← j.getObjValByPathM ["ret", "x"]
  let (retName, returnType) := retBinder
  let requiresObj ← j.getArrByPathM ["exec_proof_check", "reqs"]
  let requires ← requiresObj.mapM (fromJsonSpanned · Exp.fromJson)
  let ensuresObj ← j.getArrByPathM ["exec_proof_check", "post_condition", "ens_exps"]
  let ensures ← ensuresObj.mapM (fromJsonSpanned · Exp.fromJson)
  let bodyObj ← j.getObjValByPathM ["exec_proof_check", "body", "x"]
  let bodyStm ← Stm.fromJson bodyObj
  return some <| ExecFn.mk name args retName returnType requires.toList ensures.toList bodyStm


def typeParamsFromJson (j : Json) : m (List String) := do
  let typeParamsArr ← j.getArrUnderKeyM "typ_params"
  -- dbg_trace s!"typeParamsFromJson: {typeParamsArr}"
  return Array.toList <| ← typeParamsArr.mapM (fun _ => do
    -- TODO: These are going to be tuples, which probably get serialized as an array
    -- CZ: not sure about the above comment
    let ident := "implementMePlease"
    return ident)


def dataFieldsForVariantFromJson (j : Json) : m (String × Typ) := do
  let name ← j.getStrUnderKeyM "name"
  -- The other two fields are `Mode` and `Visibility`, which we ignore
  let ⟨fArr, _⟩ ← j.getArrUnderKeyWithSizeGeM "a" 3
  let typ ← Typ.fromJson fArr[0]
  return (name, typ)


def Struct.fromJson (j : Json) : VParser (Option Struct) := do
  let name ← pathedNameFromNameJson j (pathKey := "Path")
  let typeParams ← typeParamsFromJson j

  -- It is acceptable for the `Vstd` datatypes not to have any fields
  -- Elaboration will test for these later, omitting their definitions
  if name.head = VstdStr then
    return none
  else
    /-
      Parse the fields of the struct, under the singleton array "variants".

      The "variants" are stored in an array because Verus places structs
      and enums into the same `DatatypeX` object. For structs, there
      is exactly one variant in the array (of the same base name as the struct),
      with its fields stored in `fields` under the 0th entry of the outer array.
    -/
    let ⟨fieldsArr, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
    let fieldsArr ← fieldsArr[0].getArrUnderKeyM "fields"
    let fields ← fieldsArr.mapM dataFieldsForVariantFromJson
    return some <| Struct.mk name typeParams fields.toList


def EnumField.fromJson (j : Json) : m EnumField := do
  let name ← j.getStrUnderKeyM "name"
  let fieldsObj ← j.getArrUnderKeyM "fields"
  let fields ← fieldsObj.mapM dataFieldsForVariantFromJson

  -- If the fields are numbers, then we have a tuple enum field
  -- CZ: not sure about the above comment
  if (fields[0]?.getD ("", .Unit)).fst = "0" then
    -- dbg_trace s!"EnumField.fromJson: {name}, fields: {fields}"
    return EnumField.tuple name <| fields.toList.map (·.snd)
  else
    return EnumField.labeled name fields.toList


def Enum.fromJson (j : Json) : VParser Enum := do
  let name ← pathedNameFromNameJson j (pathKey := "Path")
  let typeParams ← typeParamsFromJson j

  /-
    The variants of an enum are stored directly in the `variants` field.
    We enforce that there should be at least one field.
  -/
  let ⟨fields, _⟩ ← j.getArrUnderKeyWithSizeGeM "variants" 1
  let fields ← fields.mapM EnumField.fromJson
  return Enum.mk name typeParams fields.toList


/--
  Calls the appropriate `fromJson` helper function based on the
  value under the `"dt_type"` key.
-/
def datatypeFromJson (j : Json) : VParser (Option Decl) := do
  let dtType ← j.getStrUnderKeyM "dt_type"
  match dtType with
  | "Enum" =>
    let enum ← Enum.fromJson j
    let enumAsDecl := Decl.enum enum
    return enumAsDecl
  | "Struct" =>
    let struct ← Struct.fromJson j
    return struct.map (Decl.struct ·)
  | "External" =>
    return none
  | _ => throw s!"Unsupported datatype: {dtType}"


/--
  Parses a JSON into a `Decl`, or throws an error.

  This function expects a top-level "wrapped" object, with appropriate
  metadata according to the type of `Decl` to be parsed.
  For example, a function-level SST is tagged with "FuncCheckSst"
  as well as the function's name.

  This function will try to parse an assert first, and if that fails,
  tries to parse a function.
-/
partial def Decl.fromJson (j : Json) : VParser (Option Decl) := do
  -- Each `Decl` JSON has a `DeclType`, which allows us
  -- to call the appropriate helper function
  let declObj ← j.getObjValM "x"
  match ← j.getStrUnderKeyM "DeclType" with
  | "Assert" => Assertion.fromJson j
  | "Datatype" => datatypeFromJson declObj
  | "SpecFn" => return (← SpecFn.fromJson declObj).map (Decl.specFn ·)
  | "ProofFn" => ProofFn.fromJson declObj
  | "ExecFn" => return (← ExecFn.fromJson declObj).map (Decl.execFn ·)
  | "Mutual" =>
    -- A mutual declaration is a list of declarations, each of which
    -- is a `DeclType` object
    let declsArr ← declObj.getArrM
    let decls ← declsArr.filterMapM (fun d => do
      match ← Decl.fromJson d with
      | none => return none
      | some decl => return some decl)
    return some <| Decl.mutualBlock decls.toList
  | s => throw s!"Unexpected declaration type: {s}"

-- CC TODO: Returning a pair of `(namespace, decls in that namespace)` limits us
--          from having multiple namespaces...
partial def Decls.fromJson? (j : Json) : VParser (String × List Decl × List Decl) := do
  let krate ← j.getStrUnderKeyM "krate"
  let krate := krate.capitalize

  let declsArr ← j.getArrUnderKeyM "decls"

  /-
    We monadically extract the `Decl` in each JSON object, from top to bottom.
    Note that we accumulate copies of these `Decls` in the state as we go
    in the hash maps, but we are assuming that the declarations are given
    to us in a good order, so there is no need to extract the objects
    back from the hash maps at the end.
  -/
  let _ ← declsArr.mapM (fun j => do
    match ← Decl.fromJson j with
    | none => return ()
    | some decl => addDecl decl)

  let defs ← getDefs
  let thms ← getThms
  return (krate, defs, thms)

partial def Decls.fromFile? (path : String) : IO (Except String (String × List Decl × List Decl)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Decls.fromJson? json default with
  | .ok decls _ => return .ok decls
  | .error e _ => return .error e

end VerusLean
