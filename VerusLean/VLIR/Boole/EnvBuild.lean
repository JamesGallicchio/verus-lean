/-
  Boole.EnvBuild — Build per-translation environments by walking decls.

  `Inference.lean` owns the read-side of these environments (`VarEnv`,
  `SpecFnMap`, `MutArgMap` plus the lookup helpers). This module owns
  the write-side: walks a `List Decl` and folds it into the appropriate
  map / env shape.

  Pure: no `BuildM`, no BooleDDM emission. Each function takes a
  starting accumulator and returns the enriched accumulator.
-/
import Std.Data.HashMap
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Inference
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.EnvBuild

open VerusLean
open VerusLean.Boole.Inference
open VerusLean.Boole.Names

/-- Collect every spec fn into a name → decl map, recursing into mutual
    blocks. Used by reveal lowering. -/
partial def collectSpecFns : List Decl → SpecFnMap
  | [] => ∅
  | d :: rest =>
    let here :=
      match d with
      | Decl.specFn f => [(f.name, f)]
      | Decl.mutualBlock ds =>
        ds.filterMap (fun d => match d with | Decl.specFn f => some (f.name, f) | _ => none)
      | _ => []
    let m := collectSpecFns rest
    here.foldl (init := m) (fun acc (k, v) => acc.insert k v)

/-- Enrich `env` with each spec fn's return type and per-parameter
    types, keyed by `fnRetKey` / `fnParamKey`. -/
def addFnRetTypes (env : VarEnv) (sfMap : SpecFnMap) : VarEnv :=
  sfMap.fold (init := env) (fun acc name sf =>
    let fnStr := identToBoole name
    let acc := acc.insert (fnRetKey fnStr) sf.returnType
    sf.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
      acc.insert (fnParamKey fnStr idx) ty))

/-- Enrich `env` with proof/exec fn parameter types, recursing into
    mutual blocks. Spec fns are covered by `addFnRetTypes`. -/
partial def addAllFnParamTypes (env : VarEnv) (decls : List Decl) : VarEnv :=
  decls.foldl (init := env) (fun acc d =>
    match d with
    | .proofFn f =>
      let fnStr := identToBoole f.name
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .execFn f =>
      let fnStr := identToBoole f.name
      f.inputs.zipIdx.foldl (init := acc) (fun acc ((_, ty), idx) =>
        acc.insert (fnParamKey fnStr idx) ty)
    | .mutualBlock ds => addAllFnParamTypes acc ds
    | _ => acc)

/-- Enrich `env` with the return type of every datatype destructor
    `<dt>..<variant>_<field>` synthesised from struct/enum decls. -/
partial def addDatatypeAccessorRetTypes (env : VarEnv) (decls : List Decl) : VarEnv :=
  decls.foldl (init := env) (fun acc d =>
    match d with
    | .struct s =>
      s.fields.foldl (init := acc) (fun acc (field, ty) =>
        let projField := projFieldNameOf s.name (datatypeNameOf s.name) field
        acc.insert (fnRetKey (datatypeDestructorNameOf s.name projField)) ty)
    | .enum e =>
      e.fields.foldl (init := acc) (fun acc field =>
        match field with
        | .labeled variant fields =>
          fields.foldl (init := acc) (fun acc (field, ty) =>
            let projField := projFieldNameOf e.name variant field
            acc.insert (fnRetKey (datatypeDestructorNameOf e.name projField)) ty)
        | .tuple variant tys =>
          tys.zipIdx.foldl (init := acc) (fun acc (ty, idx) =>
            let projField := projFieldNameOf e.name variant (toString idx)
            acc.insert (fnRetKey (datatypeDestructorNameOf e.name projField)) ty))
    | .mutualBlock ds => addDatatypeAccessorRetTypes acc ds
    | _ => acc)

/-- Names of all spec/proof/exec fns / `func`s with zero source
    parameters. Used so call-site translation can strip Verus's
    sentinel `Box(Int(0))` argument from no-param fn calls. -/
partial def collectNoParamFnNamesFromDecls : List Decl → List String
  | [] => []
  | d :: rest =>
    let here :=
      match d with
      | .specFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .proofFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .execFn f => if f.inputs.isEmpty then [identToBoole f.name] else []
      | .func f => if f.decls.isEmpty then [identToBoole f.name] else []
      | .mutualBlock ds => collectNoParamFnNamesFromDecls ds
      | _ => []
    (here ++ collectNoParamFnNamesFromDecls rest).eraseDups

/-- For every `execFn`, record which input slots are `&mut` references.
    Used by call-site translation to rewrite `f(..., &mut x, ...)` into
    a multi-output call binding. -/
partial def collectMutArgMapFromDecls (decls : List Decl) : MutArgMap :=
  let rec go (acc : MutArgMap) : List Decl → MutArgMap
    | [] => acc
    | d :: rest =>
      let acc' :=
        match d with
        | .execFn f =>
          let infos := mutArgInfos f.inputs
          if infos.isEmpty then acc else acc.insert (identToBoole f.name) infos
        | .mutualBlock ds => go acc ds
        | _ => acc
      go acc' rest
  go (∅ : MutArgMap) decls

end VerusLean.Boole.EnvBuild
