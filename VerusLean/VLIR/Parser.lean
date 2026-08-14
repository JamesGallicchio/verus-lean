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

private def isVstdName (name : Ident) : Bool :=
  let h := name.head
  h == "vstd" || h == VstdStr

/--
  The parsing monad for Verus JSONs,
  which includes a state with a map from variable names to types.

  All exceptions are strings.

  The state is a mapping from variable names to their (primitive) types.
  For example, an unsigned integer of width 32 (in Rust, a `u32`) would be `UInt 32`.

  TODO: handle shadowing
-/
structure ParserState where
  /-- Capitalized crate namespace for the top-level JSON file currently parsed.
      Used to distinguish in-crate trait impls from std/vstd/core impls that
      may appear in `resolved_method` but should stay on existing built-in
      lowering paths. -/
  currentKrate : String := ""
  expectedType : Typ := .Bool
  /-- Set while parsing the direct child of an `as int` / `as nat` `Clip`.
      Suppresses the synthesized arithmetic-promotion `Clip` on that child:
      the source already coerces it to the int/nat domain, so the existing
      lowering handles the operands (and keeps `nat.sub`/`nat.add` native). -/
  parentIntNatClip : Bool := false
  freeVars : VarMap := {}
  locVars : VarMap := {}
  -- Acts like a stack?
  boundVars : List (String × Typ) := []
  defs : DeclMap := {}
  thms : DeclMap := {}
  defsInRevOrder : List Ident := []
  thmsInRevOrder : List Ident := []
  /-- Call-site type signatures collected during parsing.
      Maps function Ident → (argTypes, returnType) for calls to
      undeclared functions (stdlib/pervasive symbols). Used by
      the auto-stub pass in ToCore to emit correctly-typed stubs. -/
  callSiteTypes : Std.HashMap Ident (List Typ × Typ) := {}
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

/-- Signal that the next-parsed child expression is the direct child of an
    `as int` / `as nat` `Clip` (see `ParserState.parentIntNatClip`). -/
def setParentIntNatClip : VParser Unit :=
  modify fun st => { st with parentIntNatClip := true }

/-- Read and clear the `parentIntNatClip` flag, so it applies to exactly one
    node (the direct child of the numeric `Clip`) and not its descendants. -/
def getAndClearParentIntNatClip : VParser Bool := do
  let st ← get
  modify fun st => { st with parentIntNatClip := false }
  return st.parentIntNatClip

def setCurrentKrate (krate : String) : VParser Unit :=
  modify fun st => { st with currentKrate := krate }

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

-- Lookup in both declaration maps: first `defs`, then `thms`.
-- Used where calls may target proof/theorem declarations as well as normal defs.
def getDeclAny? (i : Ident) : VParser (Option Decl) := do
  let st ← get
  match st.defs.get? i with
  | some d => return some d
  | none => return st.thms.get? i

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

def archWordBitWidth : Nat := 64

def xJsonFromSpanned (j : Json) : m Json :=
  match j.getObjVal? "x" with
  | .ok v => return v
  | .error _ => throw s!"Expected spanned JSON object with key `x`, got: {j}"

def widthFromJson (j : Json) : m Nat := do
  try
    j.getNatUnderKeyM "Width"
  catch _ => return archWordBitWidth -- ArchWordSize fallback

def pathedNameFromJson (j : Json) (pathKey : String := "path") : m Ident := do
  let pathVal ← j.getObjValM pathKey
  let (krate, segments) ←
    match pathVal with
    | .obj _ =>
      -- Some Verus-generated names (notably anonymous closures) encode
      -- `krate: null`. Keep parsing by assigning a stable pseudo-namespace.
      -- `krate` is upstream's `CrateId`: unit variants (`Internal`/`Core`/`Alloc`/`Vstd`)
      -- serialize as plain strings, while `Id(name, _)` serializes as `{"Id": [name, hash]}`.
      -- A bare string or `null` is also accepted (the `Option Ident` encoding).
      let krateJson ←
        match pathVal.getObjVal? "krate" with
        | .ok v => pure v
        | .error _ => pure Json.null
      let krate ←
        match krateJson with
        | .str s => pure (if s == "Internal" then "anonymous" else s)
        | .null => pure "anonymous"
        | .obj _ =>
          match krateJson.getObjVal? "Id" with
          | .ok (.arr a) =>
            match a[0]? with
            | some (Json.str name) => pure name
            | _ => throw s!"expected crate name in `krate` Id array, got {krateJson}"
          | _ => throw s!"unexpected `krate` object, got {krateJson}"
        | other => throw s!"expected string, null, or CrateId object `krate`, got {other}"
      let segsJson ← pathVal.getArrUnderKeyM "segments"
      let segs ← segsJson.mapM Json.getStrM
      pure (krate, segs.toList)
    | .str s =>
      -- Some exports encode paths as strings like `simple_pptr::PPtr`.
      -- Treat the first segment as a pseudo-crate and the rest as path segments.
      match (s.splitOn "::").filter (fun p => !p.isEmpty) with
      | kr :: segs => pure (kr, segs)
      | [] => throw s!"expected non-empty path string under key `{pathKey}`, got {s}"
    | _ => throw s!"expected object or string path under key `{pathKey}`, got {pathVal}"
  let krate := String.capitalize krate
  let ident := Lean.Name.str .anonymous krate
  -- Verus path segments may include capitalization and internal markers
  -- (notably in vstd) that are not stable as user-facing names. Normalize
  -- here so parsed identifiers are deterministic across exports.
  -- TODO: retain both raw and normalized names in VLIR.
  let isVstd := krate = VstdStr -- skip capitalized namespace if vstd
  let name := segments.foldl (init := ident) (fun acc name =>
    let nameCap := name.capitalize
    -- skip the middle capitalized name segment if we have a Vstd name
    if isVstd && name = nameCap then
      acc
    else if isVstd && name.contains '%' then
      -- A `%` in a vstd segment marks a Verus-internal suffix
      -- (e.g. `len%returns_clause_autospec` denotes the autospec view
      -- of the exec function `len`).  Keep the prefix before `%` so the
      -- autospec resolves to the same identifier as the underlying
      -- function.  Internal impl path segments such as `impl&%0` remain
      -- path scaffolding and should still be skipped.
      let head := (name.splitOn "%").headD ""
      if head.isEmpty || head.contains '&' then acc
      else Lean.Name.str acc head.capitalize
    else
      Lean.Name.str acc nameCap)

  -- De-capitalize most functions (unless it's `Vstd.X`)
  if isVstd && Ident.numSegments name ≤ 2 then
    return name
  else
    return Ident.mapTail String.decapitalize name

def pathedNameFromNameJson (j : Json) (nameKey : String := "name") (pathKey : String := "path") : m Ident := do
  let nameObj ← j.getObjValM nameKey
  pathedNameFromJson nameObj pathKey

/-- When a declaration's `kind` is `TraitMethodImpl`, return the abstract trait
    method it implements (`kind.TraitMethodImpl.method.path`).  `none` for
    abstract `TraitMethodDecl`s, inherent methods, and free functions.  The
    translator uses this to pair a trait-method impl's resolved return type with
    the abstract declaration's associated-type projection (`<Self as Trait>::Assoc`). -/
def traitImplMethodFromJson? (j : Json) : m (Option Ident) := do
  match Lean.Json.getObjValByPath j ["kind", "TraitMethodImpl"] with
  | .ok tmi =>
    match Lean.Json.getObjValByPath tmi ["method", "path"] with
    | .ok _ => some <$> pathedNameFromNameJson tmi "method" "path"
    | .error _ => pure none
  | .error _ => pure none

/-- True when a declaration's `kind` is the abstract trait-side
    `TraitMethodDecl` (both the unit-variant and payload-object JSON shapes). -/
def isTraitMethodDeclFromJson (j : Json) : Bool :=
  match j.getObjVal? "kind" with
  | .ok (.str s) => s == "TraitMethodDecl"
  | .ok kind => (kind.getObjVal? "TraitMethodDecl").isOk
  | .error _ => false

/-- Parse Verus's `Option (Fun, Typs)` resolved-method payload and return the
    selected concrete impl method path, when present. -/
def resolvedFunPayloadFromJson? (j : Json) : m (Option Ident) := do
  match j with
  | .arr elems =>
    match elems[0]? with
    | some fn => some <$> pathedNameFromJson fn "path"
    | none => pure none
  | _ => pure none

/-- Statement-level calls carry their resolved trait target under the
    `resolved_method` field. -/
def resolvedFunFromJson? (j : Json) : m (Option Ident) := do
  match j.getObjVal? "resolved_method" with
  | .ok payload => resolvedFunPayloadFromJson? payload
  | .error _ => pure none

/-- Prefer Verus's resolved trait target only when it names an already-parsed
    in-crate declaration. This keeps std/core/vstd resolved impls on the
    existing abstract/built-in lowering paths, where the translator has special
    handling for Clone/Deref/Iterator/View/etc. The parser is still single-pass:
    calls to impl declarations that appear later in the JSON remain abstract
    until declaration indexing becomes two-pass. -/
def selectResolvedCallName (fallback : Ident) (resolved? : Option Ident) : VParser Ident := do
  match resolved? with
  | some resolved =>
    let st ← get
    if st.currentKrate != "" && resolved.head == st.currentKrate then
      match ← getDeclAny? resolved with
      | some _ => pure resolved
      | none => pure fallback
    else
      pure fallback
  | none => pure fallback

/-- Peel `Box`/`Unbox` coercion wrappers off an operand.  Verus boxes the
    arguments of a generic trait-method call (`Self`/`Rhs` are type
    parameters); the native `Binary` form the arith-operator rewrite targets
    takes the bare operands, matching how unsigned `/`/`%` are already emitted. -/
partial def stripBoxExp : Exp → Exp
  | .Unary (.Box _) e => stripBoxExp e
  | .Unary (.Unbox _) e => stripBoxExp e
  | e => e

/-- A fixed-width machine integer type (`uN`/`iN`/`usize`/`isize`), peeling
    reference/box decorations.  `int`/`nat` are excluded: they are spec-only
    and never reach an exec operator-trait call. -/
partial def isMachineIntTyp : Typ → Bool
  | .UInt _ | .SInt _ | .USize | .ISize => true
  | .Decorated _ t => isMachineIntTyp t
  | _ => false

/-- Rewrite an exec call to a primitive-integer arithmetic operator-trait
    method (`core::ops::arith::{Div,Rem}::{div,rem}`) into the equivalent
    native `Binary` arithmetic, or `none` when it is not such a call.

    Rust lowers *signed* `/` and `%` to these trait calls because its signed
    division and remainder truncate toward zero; unsigned `/`/`%` and all of
    `+`/`-`/`*` are already emitted as native `Binary`, so only signed `/`/`%`
    arrive here.  They lower to the dedicated `TruncDiv`/`TruncRem` ops — Rust's
    run-time truncation, distinct from Verus's Euclidean spec `/`/`%` — which
    the Boole translator maps to `sdiv`/`smod` (SMT `bvsdiv`/`bvsrem`).  Keeping
    exec on its own ops means it stays correct even if the Euclidean spec ops
    are ever given genuine Euclidean lowering; today the two coincide because
    Strata has only the truncated bitvector operations.

    Gated on a machine-integer receiver so a user type's `Rem`/`Div` impl —
    whose call carries the identical trait path but a struct/enum operand — is
    left untouched.  Once the call is gone the abstract `Rem::rem`/`Div::div`
    trait-method decl is unreferenced and `pruneUnreferencedTraitMethodDecls`
    drops it; it otherwise names an undeclared associated `Output` type. -/
def rewriteArithTraitCall? (fnName : Ident) (recvTy? : Option Typ)
    (args : List Exp) : Option Exp :=
  match recvTy? with
  | some ty =>
    if !isMachineIntTyp ty then none else
    match fnName.toString, args with
    | "Core.Ops.Arith.Div.div", [a, b] =>
      some (.Binary (.Arith .TruncDiv .Exec) (stripBoxExp a) (stripBoxExp b))
    | "Core.Ops.Arith.Rem.rem", [a, b] =>
      some (.Binary (.Arith .TruncRem .Exec) (stripBoxExp a) (stripBoxExp b))
    | _, _ => none
  | none => none

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

private def constIntNatFromJson? (j : Json) : Option Nat :=
  match j.getObjVal? "ConstInt" with
  | .error _ => none
  | .ok v =>
    match v.getArr? with
    | .error _ => none
    | .ok arr =>
      match arr[0]?, arr[1]? with
      | some signJson, some limbsJson =>
        match signJson with
        | Json.num signNum =>
          if signNum.exponent != 0 then none else
          match signNum.mantissa with
          | 0 => some 0
          | 1 =>
            match limbsJson.getArr? with
            | .error _ => none
            | .ok limbs =>
              let base : Nat := 4294967296
              let rec go (i : Nat) (weight acc : Nat) : Option Nat :=
                if h : i < limbs.size then
                  match limbs[i].getNat? with
                  | .ok limb => go (i + 1) (weight * base) (acc + limb * weight)
                  | .error _ => none
                else
                  some acc
              go 0 1 0
          | _ => none
        | _ => none
      | _, _ => none

partial def Typ.fromJson (j : Json) : m Typ := do
  match j.getStr? with
  | .ok "Bool" => return .Bool
  | .ok "Int" => return .Int
  | .ok "Nat" => return .Nat
  | .ok "Char" => return .Char
  | .ok "USize" => return .USize
  | .ok "ISize" => return .ISize
  | .ok _ => throw s!"unsupported primitive type string: {j}"
  | .error _ =>
    match ← j["Primitive", "Int", "ConstInt", "Datatype", "Boxed", "Decorate", "Air", "Bool", "SpecFn", "TypParam", "Projection", "FnDef", "Float", "MutRef"] with
    | ("MutRef", obj) =>
      -- The dedicated `&mut T` type maps to the `Decorate(.MutRef, _, T)`
      -- representation so both encodings lower identically downstream.
      let ty ← Typ.fromJson obj
      return .Decorated .MutRef ty
    | ("Primitive", obj) =>
      let t ← obj.getArrM
      match t[0]? with
      | some j =>
        match j.getStr? with
        | .ok "StrSlice" => return .StrSlice
        | .ok "Slice" =>
          let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
          let elemTys ← arr[1].getArrM
          if h : elemTys.size ≥ 1 then
            return .Array (← Typ.fromJson elemTys[0]) none
          else
            throw s!"slice primitive missing element type: {obj}"
        | .ok "Global" => return .AirNamed "Global"
        | .ok "Array" =>
          -- In Verus, arrays are specified by their element type and length.
          -- Preserve literal const lengths in VLIR so Boole lowering can keep
          -- `[T; N]` distinct from `[T; M]`.
          let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
          let ⟨arrTyp, _⟩ ← arr[1].getArrWithSizeGeM 2
          let typ ← Typ.fromJson arrTyp[0]
          let len? := arrTyp[1]?.bind constIntNatFromJson?
          return .Array typ len?
        | _ => throw s!"unsupported primitive type: {j}"
      | none => throw s!"error, json: {obj}"

    | ("Int", obj) =>
      -- First, we check if the the underlying string is "Int" for mathematical integers
      match obj.getStr? with
      | .ok "Int" => return .Int
      | .ok "Nat" => return .Nat
      | .ok "Char" => return .Char
      | .ok "USize" => return .USize
      | .ok "ISize" => return .ISize
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

    | ("ConstInt", _obj) =>
      -- Type-level integer constants (e.g. const generics) are not first-class
      -- types in VLIR. Preserve an explicit placeholder instead of silently
      -- coercing to `Int`.
      -- TODO: add explicit const-generic support in VLIR `Typ`.
      return .AirNamed "Unsupported.ConstInt"

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
        | 1 =>
          -- Verus occasionally emits unary tuple carriers in type positions.
          -- Preserve the payload type directly.
          let ⟨typArray, _⟩ ← arr[1].getArrWithSizeGeM 1
          Typ.fromJson typArray[0]
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
    | ("Bool", _) => return .Bool
    | ("Projection", obj) =>
      -- Encode `<T as Trait>::Assoc` as a nominal type constructor
      -- `Trait.Assoc<T...>` in VLIR.
      -- TODO: introduce a dedicated associated-type node in `Typ` instead of
      -- reusing `Struct`, so downstream passes can distinguish the forms.
      let traitPath ← pathedNameFromJson obj "trait_path"
      let assocName ← obj.getStrUnderKeyM "name"
      let argsJson ← obj.getObjValM "trait_typ_args"
      let argsArr ← argsJson.getArrM
      let args ← argsArr.mapM Typ.fromJson
      return .Struct (.str traitPath assocName) args.toList
    | ("FnDef", obj) =>
      -- Function-item types (e.g., trait method items) are represented as
      -- explicit placeholder types, preserving path information for debugging.
      -- TODO: add a dedicated VLIR `Typ.FnDef` node when downstream uses it.
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let fnPath ← pathedNameFromJson arr[0]
      return .AirNamed s!"Unsupported.FnDef.{fnPath}"
    | ("Float", obj) =>
      -- VLIR does not model floats yet; preserve width as a named placeholder.
      return .AirNamed s!"Unsupported.Float{← obj.getNatM}"

    | _ => throw s!"unsupported primitive type object: {j}"

/--
  Parses a "span" object and forwards the underlying data to a given function `fj`.

  Also adds the type annotation for the span to the state.
  This annotation should be added to the state's `HashMap` when encountering a `Var`.
-/
def fromJsonSpanned {α : Type} (j : Json) (fj : Json → VParser α) : VParser α := do
  -- CC (4/15/25) some expressions are commands, and don't have types(?)
  match j.getObjVal? "typ" with
  | .ok typObj => setTyp <| ← Typ.fromJson typObj
  | _ => setTyp (← getTyp) -- no-op: keep current expected type when absent
  -- TODO: move expected-type threading to explicit parameters to avoid hidden state coupling.
  fj <| ← xJsonFromSpanned j

--------------------------------------------------------------------------------

def Mode.fromJson (j : Json) : m Mode := do
  match ← j.getStrM with
  | "Spec"  => return .Spec
  | "Proof" => return .Proof
  | "Exec"  => return .Exec
  | str => throw s!"[Mode.fromJson?]: Expected one of \{ Spec, Proof, Exec }, got {str}"

/--
  Binary-op auxiliary payloads (overflow/div0/bitshift behavior) are serialized
  differently across Verus versions. VLIR currently stores only a coarse mode,
  so convert behavior payloads to a conservative mode marker.
-/
def opBehaviorToMode (j : Json) : Mode :=
  match j.getStr? with
  | .ok "Spec" => .Spec
  | .ok "Proof" => .Proof
  | .ok "Exec" => .Exec
  | .ok _ => .Exec
  | .error _ => .Exec

def AssertQueryMode.fromJson (j : Json) : m AssertQueryMode := do
  match ← j.getStrM with
  | "NonLinear" => return .NonLinear
  | "BitVector" => return .BitVector
  | other => return .Other other

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
  match ← j["Bool", "Int", "StrSlice", "Char", "Float64", "Float32"] with
  | ("Bool", v) => return Const.Bool <| ← v.getBoolM
  | ("Int", v) =>
    -- Ints are serialized as an array, with the first element the sign enum
    -- and the second value is the data, an array of u64s.
    let ⟨arr, _⟩ ← v.getArrWithSizeGeM 2
    let s := arr[0]
    let n := arr[1]
    let sign : _root_.Int ←
      match s with
      | .num num =>
        if num.exponent == 0 then
          pure num.mantissa
        else
          throw s!"[Const.fromJson?]: unexpected non-integer sign encoding: {s}"
      | _ => throw s!"[Const.fromJson?]: expected integer sign encoding, got {s}"
    -- Reconstruct a multi-limb bigint from base-2^32 limbs (little-endian).
    -- JSON: `[sign, [limb0, limb1, ...]]` where each limb ∈ [0, 2^32).
    -- Value = limb0 + limb1·2^32 + limb2·2^64 + …
    let reassembleLimbs (limbs : Array Json) : m Nat := do
      let base : Nat := 4294967296  -- 2^32
      let mut result : Nat := 0
      let mut weight : Nat := 1
      for limb in limbs do
        let v ← limb.getNatM
        result := result + v * weight
        weight := weight * base
      return result
    -- Current Verus bigint sign encoding uses {-1, 0, 1}.
    match sign with
    | 0 =>
      -- no sign → zero
      return Const.Int 0
    | 1 =>
      -- positive number
      let nArr ← n.getArrM
      let val ← reassembleLimbs nArr
      return Const.Int <| Int.ofNat val
    | -1 =>
      -- negative number
      let nArr ← n.getArrM
      let val ← reassembleLimbs nArr
      return Const.Int <| -(Int.ofNat val)
    | _ => throw "[Const.fromJson?]: Expected an Int sign of -1, 0, or 1"
  | ("StrSlice", v) => return .StrSlice <| ← v.getStrM
  | ("Char", v) =>
    match v.getStr? with
    | .ok s =>
      match s.toList with
      | [c] => return .Char c
      | _ => throw s!"expected char literal as one-character string, got {s}"
    | .error _ => throw s!"expected char literal as one-character string, got {v}"
  | ("Float64", v) =>
    -- Verus exports float literals as raw IEEE-754 bit-patterns.
    -- VLIR has no dedicated float literal node yet, so keep the payload as an
    -- integer constant to avoid parse failure and preserve the bit pattern.
    return .Int (Int.ofNat (← v.getNatM))
  | ("Float32", v) =>
    -- Same representation strategy as Float64.
    return .Int (Int.ofNat (← v.getNatM))
  | _ => throw "[Const.fromJson?]: Unexpected match"

def Bitwise.fromJson (j : Json) : m BitwiseOp :=
  match j.getStr? with
  | .ok "BitXor" => return .BitXor
  | .ok "BitAnd" => return .BitAnd
  | .ok "BitOr"  => return .BitOr
  | .ok str => throw s!"[Bitwise.fromJson?]: Expected one of \{ BitXor, BitAnd, BitOr }, got {str}"
  | .error _ => do
    -- Shift operators are encoded as objects carrying width/sign-extension data.
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
  | s => throw s!"[ArithOp.fromJson?]: Expected one of \{ Add, Sub, Mul, EuclideanDiv, EuclideanMod }, got {s}"

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
  | .ok "MutRefCurrent" => return .MutRefCurrent
  | .ok "MutRefFuture" => return .MutRefFuture
  | .ok s => throw s!"[UnaryOp.fromJson?]: Expected one of \{ Not, BitNot, Clip, MutRefCurrent, MutRefFuture }, got {s}"
  | .error _ =>
    match ← j["BitNot", "Trigger", "Clip", "InferSpecForLoopIter", "MutRefFuture", "Length"] with
    | ("BitNot", obj) => -- Try seeing if "BitNot" has a width
      let width ← widthFromJson obj
      return .BitNot width
    | ("Trigger", _) => return .Trigger
    | ("Clip", obj) =>
      let range ← IntRange.fromJson <| ← obj.getObjValM "range"
      let truncate ← obj.getBoolUnderKeyM "truncate"
      return .Clip range truncate
    | ("InferSpecForLoopIter", _) =>
      -- Verus hint wrapper used around expressions in some loop contexts.
      -- It does not change expression semantics for our translation.
      return .Trigger
    | ("MutRefFuture", _) =>
      -- Object form carries the surface-syntax source name (e.g. "Final");
      -- the semantics is the same future-value read either way.
      return .MutRefFuture
    | ("Length", _) =>
      -- Verus distinguishes array vs slice in the payload; both are modeled as
      -- sequences by the Boole backend, so the same VLIR op suffices here.
      return .Length
    | _ => throw s!"[UnaryOp.fromJson?]: Expected one of \{ BitNot, Trigger }, got {j}"

/-- Parse Verus field-projection check metadata. -/
def VariantCheck.fromJson (j : Json) : m VariantCheck := do
  match ← j.getStrM with
  | "None" => return .None
  | "Yes" => return .Yes
  | s => throw s!"[VariantCheck.fromJson?]: expected one of None/Yes, got {s}"

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
  match j.getStr? with
  | .ok "AutoDecreases" | .ok "AutoLoopEnsures" =>
    -- Verus metadata markers used while constructing/checking loops; they
    -- unwrap to the inner expression in Verus' AIR lowering.
    return .Trigger
  | .ok s => throw s!"unsupported unaryop string: {s}"
  | .error _ =>
  match ← j["Field", "IsVariant", "Box", "Unbox", "HasType", "CustomErr", "HasResolved", "ProofNote", "ToDyn", "AutoDecreases", "AutoLoopEnsures"] with
  | ("Field", obj) =>
    try
      let dt ← pathedNameFromJson (pathKey := "Path") <| ← obj.getObjValM "datatype"
      let variant ← obj.getStrUnderKeyM "variant"
      let field ← obj.getStrUnderKeyM "field"
      let getVariant :=
        match obj.getBoolUnderKey? "get_variant" with
        | .ok b => b
        | .error _ => false
      let check ←
        match obj.getObjVal? "check" with
        | .ok checkJson => VariantCheck.fromJson checkJson
        | .error _ => pure .None
      -- dbg_trace s!"[Elab.lean]: Proj: {dt} {variant} {field}"
      return .Proj dt variant field getVariant check
    catch _ => -- see if it's a tuple
      try
        let dt ← obj.getObjValM "datatype"
        let size ← dt.getNatUnderKeyM "Tuple"
        let fieldStr ← obj.getStrUnderKeyM "field"
        let some field := fieldStr.toNat?
          | throw s!"[UnaryOp.oprFromJson?]: expected numeric tuple field, got {fieldStr}"
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
        let variantStr ← obj.getStrUnderKeyM "variant"
        let fieldFromDot := (variantStr.splitOn ".").getLast?.bind String.toNat?
        let fieldFromTuplePct :=
          if variantStr.startsWith "tuple%" then
            (variantStr.drop 6).toNat?
          else
            none
        let fieldFromPctTail := (variantStr.splitOn "%").getLast?.bind String.toNat?
        let some field := fieldFromDot <|> fieldFromTuplePct <|> fieldFromPctTail
          | throw s!"[UnaryOp.oprFromJson?]: expected tuple variant suffix to end with a number, got {variantStr}"
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
  | ("CustomErr", _) =>
    -- Error payload wrapper; no semantic effect on the expression itself.
    return .Trigger
  | ("HasResolved", _) =>
    -- Type-resolution marker (Verus-internal); erase to identity on the operand.
    return .Trigger
  | ("ProofNote", _) =>
    -- Proof-annotation marker; no semantic effect on the expression.
    return .Trigger
  | ("ToDyn", _) =>
    -- `dyn` coercion marker; erase to identity on the operand.
    return .Trigger
  | ("AutoDecreases", _) | ("AutoLoopEnsures", _) =>
    -- See the string-form arm above.
    return .Trigger
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
    match ← j["Eq", "Inequality", "Bitwise", "Arith", "HeightCompare", "Index"] with
    | ("Eq", obj)         => return .Eq (← Mode.fromJson obj)
    | ("Inequality", obj) => return .Inequality (← InequalityOp.fromJson obj)
    | ("Bitwise", obj) =>
      -- Current Verus encoding: `[bitwise_op, behavior]`.
      let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
      let op ← Bitwise.fromJson arr[0]
      let mode := opBehaviorToMode arr[1]
      return .Bitwise op mode
    | ("Arith", obj) =>
      -- Current Verus encoding: `{arith_op: behavior}`.
      match obj.getFirstVal ["Add", "Sub", "Mul", "EuclideanDiv", "EuclideanMod"] with
      | .ok (opName, payload) =>
        let op ← ArithOp.fromJson (.str opName)
        let mode := opBehaviorToMode payload
        return .Arith op mode
      | .error _ =>
        throw s!"[BinaryOp.fromJson?]: expected Arith payload as object keyed by op name, got {obj}"
    | ("HeightCompare", obj) =>
      let strictlyLt ← obj.getBoolUnderKeyM "strictly_lt"
      return .Inequality (if strictlyLt then .Lt else .Le)
    | ("Index", _) =>
      -- Verus carries `[Array|Slice, BoundsCheck]`; both lower to
      -- Sequence.select in Boole, and Verus has already generated the
      -- relevant bounds obligations.
      return .Index
    | _ => throw s!"unsupported binary op: {j}"

def Quant.fromJson (j : Json) : m Quant := do
  match ← j.getObjValM "quant" with
  | "Forall" => return .Forall
  | "Exists" => return .Exists
  | s => throw s!"[Quant.fromJson?]: Expected one of \{ Forall, Exists }, got {s}"

def CallFun.fromJson (j : Json) : VParser CallFun := do
  match ← j["Fun", "Recursive", "InternalFun"] with
  | ("Fun", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 1
    let name ← pathedNameFromJson arr[0]
    let resolved? ←
      match arr[1]? with
      | some payload => resolvedFunPayloadFromJson? payload
      | none => pure none
    let name ← selectResolvedCallName name resolved?
    return .Fun name
  | ("Recursive", obj) =>
    let name ← pathedNameFromJson obj
    return .Recursive name
  | ("InternalFun", obj) =>
    return .Fun <| String.toName <| ← obj.getStrM
  | s => throw s!"unexpected {s}"

private def decodeVarNameJson (j : Json) : m String := do
  let ⟨arr, _⟩ ← j.getArrWithSizeGeM 2
  let ident ← arr[0].getStrM
  match ident with
  | "tmp%" => return s!"tmp{← arr[1].getNatUnderKeyM "VirTemp"}"
  | "tmp%%" =>
    -- Renumbered temps appear in some exports as `tmp%%` with `VirRenumbered`.
    match arr[1].getObjVal? "VirRenumbered" with
    | .ok renObj => return s!"tmp_ren{← renObj.getNatUnderKeyM "id"}"
    | .error _ => return "tmp_ren"
  | _ =>
    -- Verus renumbers shadowing rebindings of a source name
    -- (`VirRenumbered { does_shadow := true, id }`).  Distinct rebindings
    -- must stay distinct Boole locals — they can carry different types
    -- (dalek's ghost `verus_tmp` has 17 nat rebindings and one bool one),
    -- and collapsing them aliases unrelated values — so the renumbering id
    -- is folded into the name.  The original binding
    -- (`does_shadow := false`) keeps the bare source name.
    match arr[1].getObjVal? "VirRenumbered" with
    | .ok renObj =>
      let doesShadow :=
        (renObj.getObjVal? "does_shadow" |>.bind Json.getBool?).toOption.getD false
      if doesShadow then
        return s!"{ident}_ren{← renObj.getNatUnderKeyM "id"}"
      else
        return ident
    | .error _ => return ident

def VarBinder.fromJson (j : Json) (key : String := "typ") : m (String × Typ) := do
  -- Decode binder names through `Var.fromJson` so renumbered temporaries like
  -- `["tmp%%", {"VirRenumbered": ...}]` stay consistent with variable uses.
  let nameJson ← j.getObjValM "name"
  let name ← decodeVarNameJson nameJson
  let typ ← Typ.fromJson <| ← j.getObjValM key
  return (name, typ)

def VarBinder.typBindersFromJson (j : Json) : m (List (String × Typ)) := do
  let (arr : _root_.Array Json) ← j.getArrM
  arr.toList.mapM (VarBinder.fromJson · "a")

def Var.fromJson (j : Json) : m String := do
  decodeVarNameJson j

private def isExplicitTriggerAnnotation : Json → Bool
  | .str "AutoTrigger" => false
  | .str "AllTriggers" => false
  | _ => true

/--
  Returns true iff the raw expression JSON for the current quantifier body
  contains explicit user-written trigger syntax.

  Verus always serializes the final trigger groups on `Bind.Quant`, including
  auto-trigger inference. To keep the Strata output closer to the source, we
  only preserve those trigger groups when the body itself still carries
  explicit trigger syntax (`#[trigger] ...` or `#![trigger ...]`).

  Nested quantifiers are treated as their own scope, so an inner manual trigger
  does not cause us to keep the outer quantifier's auto-generated triggers.
-/
private partial def expJsonHasUserTriggerSyntax (j : Json) : Bool :=
  let nestedQuantBody :=
    match j.getObjVal? "Bind" with
    | .ok bindJson =>
      match bindJson.getArr? with
      | .ok arr =>
        match arr.toList with
        | bindNode :: _ =>
          match Json.getObjVal? bindNode "x" with
          | .ok bindX =>
            match Json.getObjVal? bindX "Quant" with
            | .ok _ => true
            | .error _ => false
          | .error _ => false
        | [] => false
      | .error _ => false
    | .error _ => false
  if nestedQuantBody then
    false
  else
    let hasWithTriggers :=
      match j.getObjVal? "WithTriggers" with
      | .ok _ => true
      | .error _ => false
    let hasExplicitTriggerUnary :=
      match j.getObjVal? "Unary" with
      | .ok unaryJson =>
        match unaryJson.getArr? with
        | .ok arr =>
          match arr.toList with
          | opJson :: _ =>
            match Json.getObjVal? opJson "Trigger" with
            | .ok payload => isExplicitTriggerAnnotation payload
            | .error _ => false
          | [] => false
        | .error _ => false
      | .error _ => false
    if hasWithTriggers || hasExplicitTriggerUnary then
      true
    else
      match j with
      | .arr arr => arr.toList.any expJsonHasUserTriggerSyntax
      | .obj obj => obj.toList.any (fun entry => expJsonHasUserTriggerSyntax entry.2)
      | _ => false


mutual /- {Bind, Exp}.fromJson -/

partial def Bind.fromJson (j : Json) : VParser Bind := do
  let obj ← xJsonFromSpanned j
  match ← obj["Quant", "Lambda", "Choose"] with
  | ("Quant", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 4
    let q ← Quant.fromJson arr[0]
    let binders ← VarBinder.typBindersFromJson arr[1]
    -- arr[2] = trigger groups: List (List TypedExpr). Parsed with `binders`
    -- in scope, matching the `Choose` case below, so a bound variable
    -- referenced inside a trigger resolves as bound rather than free.
    let triggerGroups ← withBoundVars binders do
      let trigArr ← arr[2].getArrM
      trigArr.toList.mapM (fun groupJson => do
        let groupArr ← groupJson.getArrM
        groupArr.toList.mapM (fun exprJson => fromJsonSpanned exprJson Exp.fromJson))
    return .Quant q binders triggerGroups
  | ("Lambda", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let binders ← VarBinder.typBindersFromJson arr[0]
    return .Lambda binders
    -- throw "not yet implemented Bind.Lambda"

  | ("Choose", obj) =>
    -- Verus shape: [binders, triggers, predicate].  Triggers are erased
    -- (matches Quant's no-trigger policy); the predicate is parsed with
    -- the binders in scope so its bvars resolve correctly.
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let binders ← VarBinder.typBindersFromJson arr[0]
    let pred ← withBoundVars binders (fromJsonSpanned arr[2] Exp.fromJson)
    return .Choose binders pred

  | s => throw s!"unexpected: {s}"

partial def Exp.fromJson (j : Json) : VParser Exp := do
  -- True iff this node is the direct child of an `as int`/`as nat` Clip.
  -- Read-and-cleared here so it scopes to this node only, not its children.
  let parentIntNatClip ← getAndClearParentIntNatClip
  -- Expect that exactly one of the enumerated options will be true
  match ← j["Const", "Var", "VarLoc", "VarAt", "StaticVar", "Loc", "Call", "CallLambda", "ExecFnByName", "Ctor", "Unary", "UnaryOpr", "Binary", "BinaryOpr", "If", "Bind", "WithTriggers", "ArrayLiteral", "MatchBlock"] with
  | ("Const", obj) =>
    -- VLIR wrapper typ is set in monad state by `fromJsonSpanned`; capture it
    -- so integer literals can stay at their source-declared width.
    let ty ← getTyp
    let c ← Const.fromJson obj
    return .Const c ty

  | ("Var", obj) =>
    let ident ← Var.fromJson obj
    addFreeVarIfNotBound ident
    return .Var ident

  | ("VarLoc", obj) =>
    let ident ← Var.fromJson obj
    addLocVar ident
    return .Var ident

  | ("VarAt", obj) =>
    -- `VarAt` carries the variable and a snapshot marker (e.g. `Pre`).
    -- Preserve `Pre` as `.Unary .Old` so later renaming passes do not rewrite
    -- `old(x)` into post-state output names.
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 1
    let ident ← Var.fromJson arr[0]
    addFreeVarIfNotBound ident
    let isPre :=
      match arr.toList with
      | _ :: marker :: _ =>
        match marker.getStr? with
        | .ok s => s == "Pre"
        | .error _ => false
      | _ => false
    if isPre then
      return .Unary .Old (.Var ident)
    else
      return .Var ident

  | ("StaticVar", obj) =>
    -- Global/static variable reference.
    let ident := (← pathedNameFromJson obj (pathKey := "path")).toString
    addFreeVarIfNotBound ident
    return .Var ident

  | ("Loc", obj) =>
    -- Newer Verus exports may wrap an expression in `Loc`.
    -- Semantically this is just a location-tagged expression; we unwrap.
    fromJsonSpanned obj Exp.fromJson

  | ("Call", obj) =>
    -- Should be an object with a function name and arguments
    -- The function's name is the 0th element, the arguments the 2nd element (an array)
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    -- Capture the return type set by `fromJsonSpanned` before inner parsing.
    let retType ← getTyp
    let callFn ← CallFun.fromJson arr[0]
    let expsJson ← arr[2].getArrM
    -- Parse each argument and capture its type annotation.
    let mut argTypes : List Typ := []
    let mut exps : List Exp := []
    for argJson in expsJson do
      let exp ← fromJsonSpanned argJson Exp.fromJson
      let argTy ← getTyp
      argTypes := argTypes ++ [argTy]
      exps := exps ++ [exp]
    -- Record the call-site type signature for auto-stub generation.
    let fnName := CallFun.name callFn
    modify fun st => { st with callSiteTypes :=
      -- Keep the first observed signature (later calls may have different
      -- instantiations for generic functions).
      -- TODO: this is an approximation; a generic function called at multiple
      -- type instantiations will only get one stub signature.  A proper fix
      -- would track all instantiations or use type parameters.
      if st.callSiteTypes.contains fnName then st.callSiteTypes
      else st.callSiteTypes.insert fnName (argTypes, retType) }
    -- A signed `/`/`%` in an expression position lowers to a native `Binary`
    -- (`rewriteArithTraitCall?`), same as in the `Stm` call path.
    match rewriteArithTraitCall? fnName argTypes.head? exps with
    | some e => return e
    | none => return .Call callFn [] exps

  | ("CallLambda", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let body ← fromJsonSpanned arr[0] Exp.fromJson
    let expsJson ← arr[1].getArrM
    let exps : Array Exp ← expsJson.mapM (fromJsonSpanned · Exp.fromJson)
    return .CallLambda body exps.toList

  | ("ExecFnByName", obj) =>
    -- Function item value used as a first-class closure-like argument.
    -- We model it as a variable-like symbolic reference.
    let ident := (← pathedNameFromJson obj).toString
    addFreeVarIfNotBound ident
    return .Var ident

  | ("Ctor", obj) =>
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    -- Tuples are encoded under `Ctor` with a `Tuple` tag in slot 0.
    match arr[0].getObjVal? "Tuple" with
    | .ok tupleObj =>
      let size ← tupleObj.getNatM
      let items ← arr[2].getArrM
      let retType ← getTyp
      let mut argTypes : List Typ := []
      let mut parsedItems : List Exp := []
      for fObj in items do
        let a ← Json.getObjValM fObj "a"
        let exp ← fromJsonSpanned a Exp.fromJson
        let itemTy ← getTyp
        argTypes := argTypes ++ [itemTy]
        parsedItems := parsedItems ++ [exp]
      let ctorName : Ident := String.toName s!"Tuple_ctor_{size}"
      modify fun st => { st with callSiteTypes :=
        if st.callSiteTypes.contains ctorName then st.callSiteTypes
        else st.callSiteTypes.insert ctorName (argTypes, retType) }
      return .TupleCtor size parsedItems -- TODO: handle tuples properly
    | .error _ =>
      let dt ← pathedNameFromJson arr[0] "Path"
      let variant ← arr[1].getStrM

      -- According to Verus, the order of fields within a `Ctor` node
      -- is unspecified, so parsing should not rely on field order.
      let fields ← arr[2].getArrM
      let parsedFields ← fields.mapM (fun fObj => do
        let name ← Json.getStrUnderKeyM fObj "name"
        let a ← Json.getObjValM fObj "a"
        let exp ← fromJsonSpanned a Exp.fromJson
        return (name, exp))

      match ← getDecl? dt with
      | some (Decl.struct _) => return .StructCtor dt parsedFields.toList
      | some (Decl.enum _) => return .EnumCtor dt variant parsedFields.toList
      | some _ => throw s!"[ExpX.fromJson]: Encountered an unexpected decl with name {dt}"
      | none =>
        -- Some imported datatypes are not declared in the current shard.
        -- Keep constructor structure by falling back to a name-based guess.
        let dtTail := (dt.toString.splitOn ".").getLastD dt.toString
        if variant.toLower == dtTail.toLower then
          return .StructCtor dt parsedFields.toList
        else
          return .EnumCtor dt variant parsedFields.toList

  | ("Unary", obj) =>
    -- A unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    let op   ← UnaryOp.fromJson arr[0]
    -- An `as int` / `as nat` Clip already coerces its child to the int/nat
    -- domain, so flag the child arithmetic not to synthesize its own
    -- promotion Clip (which would force a redundant int round-trip and
    -- displace the native `nat.sub`/`nat.add` lowering).  `as uN` casts do
    -- NOT set the flag: there the int value must still be computed before the
    -- narrowing wrap.
    match op with
    | .Clip .Int _ | .Clip .Nat _ => setParentIntNatClip
    | _ => pure ()
    let data ← fromJsonSpanned arr[1] Exp.fromJson
    return .Unary op data

  | ("UnaryOpr", obj) =>
    -- A complex unary object should be an array with an op and a data element
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    -- `HasResolved(t, e)` is Verus's bool-valued mut-ref resolution predicate,
    -- assumed at control points by the prophecy machinery. Boole's model has
    -- no resolution state, so the predicate is trivially `true` here; that
    -- only weakens assumptions (and discharges resolution obligations that
    -- Boole does not track), never introduces a fact.
    if (arr[0].getObjVal? "HasResolved").isOk then
      return .Const (.Bool true) .Bool
    let retType ← getTyp
    -- dbg_trace s!"UnaryOpr arr: {arr}"
    let op  ← UnaryOp.oprFromJson arr[0]
    -- dbg_trace s!"UnaryOpr op: {op}"
    let data ← fromJsonSpanned arr[1] Exp.fromJson
    let dataTy ← getTyp

    match op with
    | .Proj' size field =>
      let projName : Ident := String.toName s!"Tuple_{size}_{field}"
      modify fun st => { st with callSiteTypes :=
        if st.callSiteTypes.contains projName then st.callSiteTypes
        else st.callSiteTypes.insert projName ([dataTy], retType) }
    | _ => pure ()

    -- Preserve both Box and Unbox: their type annotations carry concrete type
    -- information for polymorphic calls.  Box(T, e) tells downstream that e
    -- has type T (used to emit typed literals like bv{64}(10)); Unbox(T, e)
    -- tells downstream that the result has type T (used by inferBitInfo to
    -- determine the BV width of generic call results).
    -- dbg_trace s!"UnaryOpr data: {data}"
    return .Unary op data

  | ("Binary", obj) =>
    -- Capture this Binary's own result type (the VLIR wrapper, set by the
    -- enclosing `fromJsonSpanned`) before the children overwrite it.
    let resultTy ← getTyp
    -- A binary object should be an array with an op and two data elements
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let op    ← BinaryOp.fromJson arr[0]
    let data₁ ← fromJsonSpanned arr[1] Exp.fromJson
    let data₂ ← fromJsonSpanned arr[2] Exp.fromJson
    let binExp := Exp.Binary op data₁ data₂
    -- Verus spec-mode `+ - * / %` on finite-width operands is *mathematical*
    -- `int`/`nat` arithmetic — it never wraps (wrapping is the distinct
    -- `wrapping_add`/`add()`), and the VLIR records that as the op's result
    -- type even though the operands stay finite-width.  Make the implicit
    -- promotion explicit: clip an int/nat-result arithmetic op to its result
    -- type, so the int/nat lowering fires (operands widened `as_int`, faithful
    -- to the unbounded sum) instead of a wrapping `bv +`.  Exec arithmetic
    -- keeps a finite-width (`uN`) result type and is left in the bv domain,
    -- where its overflow obligation is handled separately.
    --
    -- Skip the synthesized Clip when this arithmetic is the direct child of an
    -- enclosing `as int`/`as nat` (`parentIntNatClip`): the source already
    -- coerces it, so the existing int/nat lowering applies — and a redundant
    -- inner Clip would force an int round-trip that displaces the native
    -- `nat.sub`/`nat.add`.  Bare contexts (where the arith would otherwise
    -- lower as wrapping bv) and `as uN` casts still get the promotion.
    if parentIntNatClip then return binExp
    match op, resultTy with
    | .Arith _ _, .Int => return .Unary (.Clip .Int false) binExp
    | .Arith _ _, .Nat => return .Unary (.Clip .Nat false) binExp
    | _, _ => return binExp

  | ("BinaryOpr", obj) =>
    -- Complex binary operators (currently observed: `ExtEq`).
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 3
    let lhs ← fromJsonSpanned arr[1] Exp.fromJson
    let rhs ← fromJsonSpanned arr[2] Exp.fromJson
    match ← Lean.Json.getFirstValM arr[0] ["ExtEq"] with
    | ("ExtEq", extEqInfo) =>
      let ⟨infoArr, _⟩ ← extEqInfo.getArrWithSizeGeM 2
      let deep ← infoArr[0].getBoolM
      let ty ← Typ.fromJson infoArr[1]
      return .Binary (.ExtEq deep ty) lhs rhs
    | _ =>
      throw s!"unsupported BinaryOpr: {arr[0]}"

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
    let bindObj ← xJsonFromSpanned arr[0]
    match ← bindObj["Quant", "Let", "Lambda", "Choose"] with
    | ("Let", letObj) =>
      /-
        Verus uses `BndX::Let(VarBinders<Exp>)`, where one `Let` can have
        multiple binders. VLIR `Bind.Let` stores a single binder, so we
        expand:

          let x := e1, y := e2 in body

        into nested binds:

          Bind (Let x e1) (Bind (Let y e2) body)
      -/
      -- TODO: if VLIR grows a multi-binder `Let` node, remove this desugaring.
      let ⟨binderArr, _⟩ ← letObj.getArrWithSizeGeM 1
      let mut parsed : List (String × Typ × Exp) := []
      let mut seen : List (String × Typ) := []
      for v in binderArr.toList do
        let nameJson ← v.getObjValM "name"
        let name ← decodeVarNameJson nameJson
        let expObj ← v.getObjValM "a"
        let typ ← Typ.fromJson <| ← expObj.getObjValM "typ"
        -- Later let-binders may reference earlier ones.
        let exp ← withBoundVars seen (fromJsonSpanned expObj Exp.fromJson)
        parsed := parsed ++ [(name, typ, exp)]
        seen := seen ++ [(name, typ)]
      let body ← withBoundVars seen (fromJsonSpanned arr[1] Exp.fromJson)
      return parsed.foldr (fun (name, typ, exp) acc => .Bind (.Let name typ exp) acc) body
    | _ =>
      let bind ← Bind.fromJson arr[0]
      let bind :=
        match bind with
        | .Quant q vars trigs =>
          if trigs.isEmpty || expJsonHasUserTriggerSyntax arr[1] then
            bind
          else
            .Quant q vars []
        | _ => bind
      let exp ← withBoundVars bind.idents (fromJsonSpanned arr[1] Exp.fromJson)
      return .Bind bind exp

  | ("WithTriggers", obj) =>
    -- `WithTriggers` still matters for trigger provenance, but the wrapper
    -- itself is erased from VLIR after parsing.
    let ⟨arr, _⟩ ← obj.getArrWithSizeGeM 2
    fromJsonSpanned arr[1] Exp.fromJson

  | ("ArrayLiteral", obj) =>
    -- `obj` should be an array with the exact elements
    let arr ← obj.getArrM
    let elems ← arr.mapM (fromJsonSpanned · Exp.fromJson)
    return .ArrayLiteral elems.toList

  | ("MatchBlock", obj) =>
    let scrutineeObj ← obj.getObjValM "scrutinee"
    let scrutinee ← fromJsonSpanned scrutineeObj Exp.fromJson
    let typ ← Typ.fromJson <| ← scrutineeObj.getObjValM "typ"
    let bodyObj ← obj.getObjValM "simplified_body"
    -- let variant ← bodyObj.getStrUnderKeyM "variant"
    let body ← fromJsonSpanned bodyObj Exp.fromJson
    return .MatchBlock (scrutinee, typ) body

  | s => throw s!"[ExpX.fromJson?]: Expected an Exp branch string, got {s}"

end /- mutual -/


/--
  Parses a `Dest` expression, but with the expectation that the result
  is an l-value. Mainly used to build `Assign`s.

  In Verus, there are several ways to store a variable identifier in an
  expression (an `Exp`): `Var`, `VarLoc`, `VarAt`, `Loc`, etc.

  This function parses the underlying `Exp` under the "dest", preserving
  projection structure instead of flattening to a synthetic name.
-/
partial def lvalueFromExp : Exp → Option LValue
  | .Var i => some (.Var i)
  | .Unary (.Proj dt variant field getVariant check) e =>
    lvalueFromExp e |>.map (fun base =>
      .Proj base dt variant field getVariant check)
  | .Unary (.Proj' size field) e =>
    lvalueFromExp e |>.map (fun base =>
      .Proj' base size field)
  | .Binary .Index base index =>
    lvalueFromExp base |>.map (fun base =>
      .Index base index)
  | .Unary (.Box _) e
  | .Unary (.Unbox _) e
  | .Unary (.Clip _ _) e
  | .Unary .Old e
  | .Unary .Trigger e
  -- Assigning through a `&mut` place (`*x = ...`) targets the place itself;
  -- the mut-ref value wrappers are transparent on the l-value side.
  | .Unary .MutRefCurrent e
  | .Unary .MutRefFuture e
  | .Unary (.HasType _) e => lvalueFromExp e
  | _ => none

def Dest.fromJson (j : Json) : VParser (LValue × Typ) := do
  let e ← fromJsonSpanned j Exp.fromJson
  -- The dest's type is the node's own `typ` field.  The parser's typ state
  -- holds whichever child parsed last — for an index place (`a[i] = …`)
  -- that is the *index*, whose `usize` would mistype the stored value.
  let ty ←
    match j.getObjVal? "typ" with
    | .ok typObj => Typ.fromJson typObj
    | .error _ => getTyp
  match lvalueFromExp e with
  | some lhs => return (lhs, ty)
  | none => throw s!"Expected an l-value expression, got {e}"

def LoopInvariant.fromJson (j : Json) : VParser LoopInvariant := do
  let atEntry ← j.getBoolUnderKeyM "at_entry"
  let atExit ← j.getBoolUnderKeyM "at_exit"
  let invObj ← j.getObjValM "inv"
  let invExp ← fromJsonSpanned invObj Exp.fromJson
  return LoopInvariant.mk atEntry atExit invExp


partial def Stm.fromJson (j : Json) : VParser Stm := do
  let declInputArity? : Decl → Option Nat
    | .specFn f => some f.inputs.length
    | .proofFn f => some f.inputs.length
    | .execFn f => some f.inputs.length
    | .assertion a => some a.decls.length
    | .func f => some f.decls.length
    | _ => none
  let isSyntheticNoParamArg : Exp → Bool
    | .Const (.Int i) _ => i == 0
    | _ => false
  let coerceIntConstArgByTyp (argJson : Json) (e : Exp) : VParser Exp := do
    -- Verus can serialize literal call arguments as mathematical ints even when
    -- the expected parameter type is fixed-width. Re-attach width/sign via
    -- `Clip` using the argument's `typ` metadata.
    -- TODO: move literal-normalization to a shared post-parse pass.
    match e with
    | .Const (.Int _) _ =>
      match Lean.Json.getObjValByPath argJson ["typ"] with
      | .ok typJson =>
        let ty ← Typ.fromJson typJson
        match ty with
        | .UInt w => pure <| .Unary (.Clip (.U (UInt32.ofNat w)) true) e
        | .SInt w => pure <| .Unary (.Clip (.I (UInt32.ofNat w)) true) e
        | .USize => pure <| .Unary (.Clip .USize true) e
        | .ISize => pure <| .Unary (.Clip .ISize true) e
        | _ => pure e
      | .error _ => pure e
    | _ => pure e
  match ← j["Call", "Assert", "AssertBitVector", "AssertQuery", "AssertCompute", "AssertLean",
    "Assume", "Assign", "DeadEnd", "Return", "BreakOrContinue", "If", "Loop",
    "OpenInvariant", "ClosureInner", "Block", "Fuel", "RevealString", "Air"] with

  | ("Call", obj) =>
    -- `fun` is a `CallTarget`: `{"Fun": <fun>}` wraps a bare `Fun` (with a `path`),
    -- or `"AssumeExternal"`. Unwrap the `Fun` tag before reading the path; a
    -- bare `Fun` object without the `CallTarget` wrapper is read directly.
    let funJson ← obj.getObjValM "fun"
    let fnName ←
      match funJson.getObjVal? "Fun" with
      | .ok funObj => pathedNameFromJson funObj "path"
      | .error _ => pathedNameFromJson funJson "path"
    -- Verus records the concrete impl a trait-method call resolves to in
    -- `resolved_method`. Dispatch to that impl only when it is an emitted
    -- in-crate declaration; external trait impls stay on the existing
    -- special-case lowering path.
    let callName ← selectResolvedCallName fnName (← resolvedFunFromJson? obj)
    let typArgsArr ← obj.getArrUnderKeyM "typ_args"
    let typArgs ← typArgsArr.mapM Typ.fromJson
    let argsArr ← obj.getArrUnderKeyM "args"
    let argsParsed ← argsArr.mapM (fun arg => do
      let e ← fromJsonSpanned arg Exp.fromJson
      coerceIntConstArgByTyp arg e)
    let args ←
      match ← getDeclAny? fnName with
      | some d =>
        match declInputArity? d, argsParsed.toList with
        | some 0, [arg] =>
          -- Verus may emit a synthetic `0` argument for no-parameter calls.
          -- If we know the callee has arity 0, drop that placeholder.
          -- TODO: replace this heuristic with an explicit export-side marker.
          if isSyntheticNoParamArg arg then
            pure []
          else
            pure argsParsed.toList
        | _, _ => pure argsParsed.toList
      | none => pure argsParsed.toList
    match obj.getObjVal? "dest" with
    | .ok .null =>
      return .Call callName typArgs.toList args
    | .ok destObj =>
      let (lhs, lhsTy) ← Dest.fromJson <| ← destObj.getObjValM "dest"
      let lhsIsInit ← destObj.getBoolUnderKeyM "is_init"
      -- Signed `/`/`%` reach here as `core::ops::arith::{Div,Rem}` calls;
      -- rewrite them to native `Binary` arithmetic (`rewriteArithTraitCall?`),
      -- gated on the receiver's annotated type (consistent with the
      -- expression-call path, which also keys on the actual operand type).
      let recvTy? ← match argsArr[0]? with
        | some a =>
          match Lean.Json.getObjValByPath a ["typ"] with
          | .ok tj => some <$> Typ.fromJson tj
          | .error _ => pure none
        | none => pure none
      let rhs := (rewriteArithTraitCall? fnName recvTy? args).getD
        (Exp.Call (.Fun callName) typArgs.toList args)
      return .Assign lhs lhsTy rhs lhsIsInit
    | .error _ =>
      return .Call callName typArgs.toList args

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
    let mode ← AssertQueryMode.fromJson <| ← obj.getObjValM "mode"
    let bodyObj ← obj.getObjValM "body"
    let stm ← fromJsonSpanned bodyObj Stm.fromJson
    return .AssertQuery mode stm

  | ("AssertCompute", obj) =>
    let e ← fromJsonSpanned obj Exp.fromJson
    return .AssertCompute e

  | ("AssertLean", obj) =>
    let bodyObj ← obj.getObjValM "body"
    let e ← fromJsonSpanned bodyObj Exp.fromJson
    -- `assert(P) by (lean_proof as <name>)` carries the user label in
    -- `mode: {"Proof": <name>}`.  Preserve it as a named query so the emitted
    -- Boole obligation keeps the source label (`assert [<name>]: P;`).
    let label : String :=
      (Lean.Json.getObjValByPath obj ["mode", "Proof"] |>.bind (·.getStr?)).toOption.getD ""
    if label.isEmpty then return .AssertLean e
    else return .AssertQuery (.Other label) (.AssertLean e)

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
    let decrease ←
      match obj.getObjVal? "decrease" with
      | .error _ => pure []
      | .ok .null => pure []
      | .ok (.arr arr) => arr.mapM (fun j => fromJsonSpanned j Exp.fromJson) |>.map (·.toList)
      | .ok j => throw s!"expected loop decrease array, got: {j.compress}"
    return .Loop isForLoop label cond body invs.toList decrease

  | ("OpenInvariant", obj) =>
    let stm ← fromJsonSpanned obj Stm.fromJson
    return .OpenInvariant stm

  | ("ClosureInner", obj) =>
    -- Closure bodies are wrapped under `body`; metadata (`typ_inv_vars`) is ignored for now.
    let stm ← fromJsonSpanned (← obj.getObjValM "body") Stm.fromJson
    return .ClosureInner stm

  | ("Block", obj) =>
    -- We enforce that the block has at least one statement
    let arr ← obj.getArrM
    let stmts ← arr.mapM (do Stm.fromJson <| ← xJsonFromSpanned ·)
    return .Block stmts.toList

  | ("Fuel", obj) =>
    -- `Fuel` JSON is `[{path: {krate, segments}}, amount]`.
    -- `reveal(f)` emits amount=1; `reveal_with_fuel(f, n)` emits amount=n.
    match obj with
    | .arr elems =>
      if elems.size ≥ 2 then
        let fnName ← pathedNameFromJson elems[0]!
        let fuel := match elems[1]! with
          | .num n => n.mantissa.toNat
          | _ => 1
        return .Reveal fnName fuel
      else
        return .Block []
    | _ => return .Block []

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
    let xJson ← xJsonFromSpanned v
    let ⟨i, ty⟩ ← VarBinder.fromJson xJson
    -- We build up the bound variables as we go (in case of dependent typing)
    pushBoundVar i ty
    return (i, ty))
  return vars.toList

private def mutRefParamNamesFromDecl (j : Json) : VParser (List String) := do
  -- In recent Verus exports, mutability for exec parameters is encoded in
  -- `decl.ens_pars[*].purpose = MutPost` rather than in `pars[*].typ`.
  -- Recover those names here so `ExecFn.fromJson` can re-attach `.MutRef`.
  match j.getArrByPath? ["decl", "ens_pars"] with
  | .error _ => pure []
  | .ok ensPars =>
    let mut names : List String := []
    for spanned in ensPars do
      let xJson ← xJsonFromSpanned spanned
      let isMutPost :=
        match xJson.getObjVal? "purpose" with
        | .ok purposeJson =>
          match purposeJson.getStr? with
          | .ok s => s == "MutPost"
          | .error _ => false
        | .error _ => false
      if isMutPost then
        let ⟨arr, _⟩ ← xJson.getArrUnderKeyWithSizeGeM "name" 1
        let name ← arr[0].getStrM
        names := name :: names
    pure names.eraseDups

private def firstIndexOfName? (names : List String) (target : String) : Option Nat :=
  names.zipIdx.findSome? (fun (n, i) => if n == target then some i else none)

private partial def peelDecreasesInitRhs : Exp → Exp
  | .Unary (.Box _) e => peelDecreasesInitRhs e
  | .Unary (.Unbox _) e => peelDecreasesInitRhs e
  | .Unary (.Clip _ _) e => peelDecreasesInitRhs e
  | .Unary (.HasType _) e => peelDecreasesInitRhs e
  | e => e

private def inputVarIdxFromDecreasesInitRhs?
    (argNames : List String) (rhs : Exp) : Option Nat :=
  match peelDecreasesInitRhs rhs with
  | .Var x => firstIndexOfName? argNames x
  | _ => none

private def recursiveCasesIdxHintFromTermCheck
    (argNames : List String) (termCheck : Json) : VParser (Option Nat) := do
  match termCheck.getArrByPath? ["local_decls_decreases_init"] with
  | .error _ => pure none
  | .ok decInit =>
    let stms ← decInit.mapM (fromJsonSpanned · Stm.fromJson)
    -- Derive the hint only from the decreases-init assignment chain,
    -- instead of scanning full ASTs.
    pure <| stms.toList.findSome? (fun
      | .Assign _ _ rhs _ => inputVarIdxFromDecreasesInitRhs? argNames rhs
      | _ => none)


def SpecFn.fromJson (j : Json) : VParser (Option SpecFn) := do
  let name ← pathedNameFromNameJson j
  -- vstd spec fns that carry a body are vstd-internal helpers whose
  -- (transitively-recursive) translations we deliberately do NOT import.
  -- But we MUST still emit the symbol as an *uninterpreted declaration* so
  -- references resolve — e.g. `vstd::arithmetic::power2::pow2`, named from
  -- the file's own specs and from preserved vstd lemma `ensures` (see
  -- `ProofFn.fromJson`).  Previously these were dropped wholesale, leaving
  -- `Unknown variable Arithmetic_Power2_pow2`.  Treat them exactly like the
  -- already-uninterpreted vstd specs (`spec_axioms: null`): keep the
  -- signature, force `body := none`.  Unreferenced / inlined-at-call-site /
  -- `Pervasive_*` vstd specs are still dropped downstream by
  -- `pruneUnreferencedVstdSpecs`, so this does not leak unused declarations.
  let dropVstdBody :=
    isVstdName name &&
      (Lean.Json.getObjValByPath j ["axioms", "spec_axioms", "body_exp"]).toOption.isSome
  let args ← fnParseArgs j
  let argNames := args.map Prod.fst

  -- TODO: This ignores other info about the return value, (a `Par` in Verus)
  let returnType ← Typ.fromJson <| ← j.getObjValByPathM ["ret", "x", "typ"]
  setTyp returnType

  -- Uninterpreted spec functions have `spec_axioms = null` and no body.
  -- We still emit them as declaration-only (body := none) so downstream
  -- code can reference them.
  let bodyExp? ←
    if dropVstdBody then pure none
    else match Lean.Json.getObjValByPath j ["axioms", "spec_axioms", "body_exp"] with
    | .ok v => some <$> fromJsonSpanned v Exp.fromJson
    | .error _ => pure none

  let isRecursive :=
    match Lean.Json.getObjValByPath j ["has", "is_recursive"] with
    | .ok (.bool b) => b
    | _ => false

  -- Parse opaqueness: `"Opaque"` vs `{"Revealed": {...}}`.
  let isOpaque :=
    match j.getObjVal? "opaqueness" with
    | .ok (.str "Opaque") => true
    | _ => false

  let traitImplMethod? ← traitImplMethodFromJson? j

  -- A spec fn's `recommends` arrive as its `decl.reqs`, the slot proof/exec
  -- fns use for `requires`.  See `SpecFn.recommends`.
  let recommends : List Exp ←
    match j.getArrByPath? ["decl", "reqs"] with
    | .ok reqArr =>
      let parsed ← reqArr.mapM (fromJsonSpanned · Exp.fromJson)
      pure parsed.toList
    | .error _ => pure []

  try
    -- let termCheckKind ← j.getObjValByPathM ["axioms", "spec_axioms", "termination_check", "post_condition", "kind"]
    -- if termCheckKind != "DecreasesImplicitLemma" then
    let termCheck : Json ← j.getObjValByPath ["axioms", "spec_axioms", "termination_check"]
    -- Keep recursive-function decreases in VLIR even though current Core lowering
    -- cannot emit function-level measures yet (documented in `specFnToCore`).
    let decreases ← fromJsonSpanned (← termCheck.getObjValM "body") Stm.fromJson
    let recursiveCasesIdxHint ← recursiveCasesIdxHintFromTermCheck argNames termCheck
    return some <| {
      name := name
      inputs := args
      returnType := returnType
      decreases := some decreases
      body := bodyExp?
      isRecursive := isRecursive
      recursiveCasesIdxHint := recursiveCasesIdxHint
      isOpaque := isOpaque
      traitImplMethod? := traitImplMethod?
      recommends := recommends
    }
  catch _ =>
    return some <| {
      name := name
      inputs := args
      returnType := returnType
      decreases := none
      body := bodyExp?
      isRecursive := isRecursive
      recursiveCasesIdxHint := none
      isOpaque := isOpaque
      traitImplMethod? := traitImplMethod?
      recommends := recommends
    }

private def localDeclOriginOfKind? (kind : Json) : Option LocalDeclOrigin :=
  if (kind.getObjVal? "Param").isOk then
    none
  else if (kind.getObjVal? "Return").isOk then
    none
  else
    match kind.getObjVal? "StmtLet" with
    | .ok stmtLet =>
      let mutable :=
        match stmtLet.getBoolUnderKey? "mutable" with
        | .ok b => b
        | .error _ => false
      some (.sourceStmtLet mutable)
    | .error _ =>
      if (kind.getObjVal? "Assert").isOk then
        some .sourceAssert
      else if (kind.getObjVal? "Decreases").isOk then
        some .sourceDecreases
      else
        match kind with
        | .obj obj =>
          match obj.toList with
          | (tag, _) :: _ => some (.sourceOther tag)
          | [] => some (.sourceOther "<empty-kind>")
        | _ => some (.sourceOther "<non-object-kind>")

def localDeclsFromJson (j : Json) : VParser (List LocalDeclInfo) := do
  match j.getArrByPath? ["exec_proof_check", "local_decls"] with -- to be extended
  | .error _ => return []
  | .ok arr =>
    let mut locals : Array LocalDeclInfo := #[]
    for decl in arr do
      let origin? :=
        match decl.getObjVal? "kind" with
        | .ok kind => localDeclOriginOfKind? kind
        | .error _ => some (.sourceOther "<missing-kind>")
      match origin? with
      | none => continue
      | some origin =>
        let name ← Var.fromJson <| ← decl.getObjValM "ident"
        let typ ← Typ.fromJson <| ← decl.getObjValM "typ"
        locals := locals.push { name := name, ty := typ, origin := origin }
    return locals.toList


/-- Extract the source-level `decreases` clause from an `exec_proof_check`
    block.  Verus emits one `Stm.Assign` per decreases term, binding a
    synthesized `decrease%initN` local to the term's value.  We preserve the
    list verbatim so downstream lowerings can pick the relevant RHS without
    re-parsing.  Returns `[]` if the JSON has no `local_decls_decreases_init`
    array (e.g. non-recursive functions). -/
private def decreasesFromExecProofCheck (j : Json) : VParser (List Stm) := do
  match j.getArrByPath? ["exec_proof_check", "local_decls_decreases_init"] with
  | .ok arr =>
    let stms ← arr.mapM (fromJsonSpanned · Stm.fromJson)
    pure stms.toList
  | .error _ => pure []

def ProofFn.fromJson (j : Json) : VParser ProofFn := do
  let name ← pathedNameFromNameJson j
  let args ← fnParseArgs j
  let (retName, returnType) ←
    match Lean.Json.getObjValByPath j ["ret", "x"] with
    | .ok retObj =>
      VarBinder.fromJson retObj
    | .error _ =>
      pure ("%return", .Unit)
  -- Declaration-level contract (`decl.reqs` / `decl.enss`).  For an external
  -- proof fn (e.g. a referenced vstd lemma) `exec_proof_check` is `null` —
  -- there is no body to check — but the *trusted contract* is still present
  -- under `decl` and MUST be preserved.  Dropping it (the old behaviour)
  -- emitted the stub procedure with an empty `spec { }`, so a downstream
  -- `call lemma_…()` injected no facts and the proof lost its axioms.
  let declReqs : List Exp ←
    match j.getArrByPath? ["decl", "reqs"] with
    | .ok reqArr =>
      let parsed ← reqArr.mapM (fromJsonSpanned · Exp.fromJson)
      pure parsed.toList
    | .error _ => pure []
  let declEnss : List Exp ←
    match j.getArrByPath? ["decl", "enss"] with
    | .ok ensGroups =>
      let mut acc : List Exp := []
      for g in ensGroups do
        match g.getArr? with
        | .ok group =>
          let parsed ← group.mapM (fromJsonSpanned · Exp.fromJson)
          acc := acc ++ parsed.toList
        | .error _ => pure ()
      pure acc
    | .error _ => pure []
  match Lean.Json.getObjValByPath j ["exec_proof_check"] with
  | .ok .null =>
    return ProofFn.mk name args retName returnType declReqs declEnss none [] []
  | .error _ =>
    return ProofFn.mk name args retName returnType declReqs declEnss none [] []
  | .ok _ =>
    pure ()

  let requiresObj ← j.getArrByPathM ["exec_proof_check", "reqs"]
  let requires ← requiresObj.mapM (fromJsonSpanned · Exp.fromJson)

  -- Prefer declaration-level ensures (`decl.enss`) so we preserve the source
  -- postconditions instead of post-elaboration query rewrites in
  -- `exec_proof_check.post_condition.ens_exps`.
  let ensures : List Exp ←
    match j.getArrByPath? ["decl", "enss"] with
    | .ok ensGroups =>
      let mut acc : List Exp := []
      for g in ensGroups do
        match g.getArr? with
        | .ok group =>
          let parsed ← group.mapM (fromJsonSpanned · Exp.fromJson)
          acc := acc ++ parsed.toList
        | .error _ => pure ()
      pure acc
    | .error _ =>
      -- Backward-compatible fallback for older JSON shapes.
      match j.getArrByPath? ["exec_proof_check", "post_condition", "ens_exps"] with
      | .ok ensuresObj =>
        let parsed ← ensuresObj.mapM (fromJsonSpanned · Exp.fromJson)
        pure parsed.toList
      | .error _ => pure []

  -- CC TODO: Still need to examine the internals for `by (lean)`
  -- If the proof function is NOT marked `by (lean)`, then we don't need to
  -- store its proof body (Verus already proved it)
  --let isLean ← j.getBoolUnderPathM ["attrs", "lean"]
  --if isLean then
  -- Parse the body as an expression
  -- For proof functions, this expression is stored in the "exec_proof_check"
  let bodyObj ← j.getObjValByPathM ["exec_proof_check", "body", "x"]
  let bodyStm ← Stm.fromJson bodyObj
  let decreases ← decreasesFromExecProofCheck j
  let locals ← localDeclsFromJson j
  return ProofFn.mk name args retName returnType requires.toList ensures bodyStm decreases locals
  --else
    --return ProofFn.mk name args requires.toList ensures.toList none


def ExecFn.fromJson (j : Json) : VParser (Option ExecFn) := do
  let name ← pathedNameFromNameJson j
  if isVstdName name then return none else
  let mutRefNames ← mutRefParamNamesFromDecl j
  let argsRaw ← fnParseArgs j
  -- Reconstruct mutable-reference typing for parameters discovered from
  -- `decl.ens_pars` metadata.
  let args :=
    argsRaw.map (fun (n, t) =>
      if mutRefNames.contains n then
        match t with
        | .Decorated .MutRef _ => (n, t)
        | _ => (n, .Decorated .MutRef t)
      else
        (n, t))
  let retBinder ← VarBinder.fromJson <| ← j.getObjValByPathM ["ret", "x"]
  let (retName, returnType) := retBinder
  let requiresObj ←
    match j.getArrByPath? ["exec_proof_check", "reqs"] with
    | .ok arr => pure arr
    | .error _ => j.getArrByPathM ["decl", "reqs"]
  let requires ← requiresObj.mapM (fromJsonSpanned · Exp.fromJson)
  let ensures ←
    match j.getArrByPath? ["exec_proof_check", "post_condition", "ens_exps"] with
    | .ok ensuresObj =>
      let ensures ← ensuresObj.mapM (fromJsonSpanned · Exp.fromJson)
      pure ensures.toList
    | .error _ =>
      let mut acc : List Exp := []
      match j.getArrByPath? ["decl", "enss"] with
      | .ok ensGroups =>
        for g in ensGroups do
          match g.getArr? with
          | .ok group =>
            let parsed ← group.mapM (fromJsonSpanned · Exp.fromJson)
            acc := acc ++ parsed.toList
          | .error _ => pure ()
        pure acc
      | .error _ => pure []
  let (bodyStm, hasExecProofBody) ←
    match Lean.Json.getObjValByPath j ["exec_proof_check", "body", "x"] with
    | .ok bodyObj =>
      match bodyObj with
      | .obj _ =>
        let bodyStm ← Stm.fromJson bodyObj
        pure (bodyStm, true)
      | _ =>
        -- Declaration-only exec fns (common for trait methods/helpers) can still
        -- be called from translated bodies. Keep them as empty-body stubs.
        pure (Stm.Block [], false)
    | .error _ =>
      -- Missing `exec_proof_check.body` is also treated as declaration-only.
      -- We intentionally preserve these declarations so calls resolve in Core.
      pure (Stm.Block [], false)
  let locals ←
    if hasExecProofBody then
      localDeclsFromJson j
    else
      pure []
  let decreases ←
    if hasExecProofBody then
      decreasesFromExecProofCheck j
    else
      pure []
  let traitImplMethod? ← traitImplMethodFromJson? j
  return some <| ExecFn.mk name args retName returnType requires.toList ensures bodyStm decreases locals traitImplMethod? (isTraitMethodDeclFromJson j)


def typeParamsFromJson (j : Json) : m (List String) := do
  let typeParamsArr ← j.getArrUnderKeyM "typ_params"
  -- Verus serializes type params as entries like `["T", "..."]`.
  -- Keep the first component (the param name) and fall back only when malformed.
  return Array.toList <| ← typeParamsArr.mapM (fun entry => do
    match entry with
    | .str s => pure s
    | .arr elems =>
      match elems[0]? with
      | some first =>
        match first with
        | .str s => pure s
        | _ => pure "implementMePlease"
      | _ => pure "implementMePlease"
    | _ => pure "implementMePlease")


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
  if isVstdName name then
    return none
  else
    /-
      Parse the fields of the struct, under the singleton array "variants".

      The "variants" are stored in an array because Verus places structs
      and enums into the same `DatatypeX` object. For structs, there
      is exactly one variant in the array (of the same base name as the struct),
      with its fields stored in `fields` under the 0th entry of the outer array.
    -/
    -- Opaque structs can appear with `variants: []` in shards.
    -- Model them as field-less structs so translation can proceed.
    let variants ← j.getArrUnderKeyM "variants"
    if variants.isEmpty then
      return some <| Struct.mk name typeParams []
    else
      match variants[0]? with
      | some v =>
        let fieldsArr ← v.getArrUnderKeyM "fields"
        let fields ← fieldsArr.mapM dataFieldsForVariantFromJson
        return some <| Struct.mk name typeParams fields.toList
      | none =>
        return some <| Struct.mk name typeParams []


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
    Some opaque/imported shards serialize as empty enums (`[]`), so we allow
    the empty case and let lowering choose a suitable Core representation.
  -/
  let fieldsObj ← j.getArrUnderKeyM "variants"
  let fields ← fieldsObj.mapM EnumField.fromJson
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
  | "Closure" =>
    -- Verus may emit closure datatypes with empty variants and `krate: null`.
    -- Keep them as empty struct-like declarations so typed references parse.
    let name ← pathedNameFromNameJson j (pathKey := "Path")
    let typeParams ← typeParamsFromJson j
    return some <| Decl.struct <| Struct.mk name typeParams []
  | "External" =>
    -- Preserve external datatypes as abstract Boole types.  Some executable
    -- scaffolding that survives translation (for example unrecovered slice
    -- iterators) still refers to these nominal types even though Verus does
    -- not expose constructors for them.
    let enum ← Enum.fromJson j
    return some (Decl.enum enum)
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
  setCurrentKrate krate

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

/-- Type alias for call-site type signatures collected during parsing. -/
abbrev CallSiteTypes := Std.HashMap Ident (List Typ × Typ)

partial def Decls.fromFile? (path : String) :
    IO (Except String (String × List Decl × List Decl × CallSiteTypes)) := do
  let jsonStr ← IO.FS.readFile path
  let json ← IO.ofExcept <| Json.parse jsonStr
  match Decls.fromJson? json default with
  | .ok (krate, defs, thms) st => return .ok (krate, defs, thms, st.callSiteTypes)
  | .error e _ => return .error e

end VerusLean
