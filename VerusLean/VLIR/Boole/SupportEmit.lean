/-
  Boole.SupportEmit — emit BooleDDM commands for translator support decls.

  The declaration inventory itself lives in `Support.lean`; this module is the
  BuildM/BooleDDM layer that turns requested support declarations into
  commands after the main user declarations have been lowered.
-/
import VerusLean.VLIR.Boole.Bld
import VerusLean.VLIR.Boole.Builder
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.Support

namespace VerusLean.Boole.SupportEmit

open Strata
open Strata.BooleDDM
open VerusLean
open VerusLean.Boole.Bld
open VerusLean.Boole.Builder
open VerusLean.Boole.Emit
open VerusLean.Boole.Support
open VerusLean.Boole.Context (SupportDecl)

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩

abbrev TypeLowerer := Typ → BuildM BType

private def mkCastFnDecl (lowerType : TypeLowerer)
    (name : String) (inputTy outputTy : Typ) : BuildM BCmd := do
  addFreeVars #[name]
  let nameAnn := ann name
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange := ann none
  let inputBinding :=
    BooleDDM.Binding.mkBinding default (ann "x")
      (BooleDDM.TypeP.expr (← lowerType inputTy))
  let inputBindings := BooleDDM.Bindings.mkBindings default (ann #[inputBinding])
  let outputTy' ← lowerType outputTy
  pure (.command_fndecl default nameAnn typeArgs inputBindings outputTy')

private def mkAbstractTypeDecl (name : String) (params : List String) : BuildM BCmd := do
  addFreeVars #[name]
  let args : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    if params.isEmpty then ann none
    else
      let bindings := params.toArray.map fun p =>
        BooleDDM.Binding.mkBinding default (ann p) (BooleDDM.TypeP.type default)
      ann (some (BooleDDM.Bindings.mkBindings default (ann bindings)))
  pure (.command_typedecl default (ann name) args)

/-- Emit the polymorphic 2-ary tuple datatype:
    `datatype Tuple (T0 : Type, T1 : Type) { Tuple_ctor_2(_0 : T0, _1 : T1) };`.
    VLIR represents tuples as nested pairs, so this single datatype covers the
    non-unit tuple surface. -/
private def mkTupleDatatypeDecl : BuildM BCmd := do
  addFreeVars #["Tuple", "Tuple_ctor_2", "Tuple.._0", "Tuple.._1"]
  let typeParamBindings : Array (BooleDDM.Binding SourceRange) := #[
    BooleDDM.Binding.mkBinding default (ann "T0") (BooleDDM.TypeP.type default),
    BooleDDM.Binding.mkBinding default (ann "T1") (BooleDDM.TypeP.type default)]
  let typeArgs : Strata.Ann (Option (BooleDDM.Bindings SourceRange)) SourceRange :=
    ann (some (BooleDDM.Bindings.mkBindings default (ann typeParamBindings)))
  let t0Idx ← resolveFreeVar "T0"
  let t1Idx ← resolveFreeVar "T1"
  let field0 :=
    BooleDDM.Binding.mkBinding default (ann "_0") (BooleDDM.TypeP.expr (fvarTy t0Idx))
  let field1 :=
    BooleDDM.Binding.mkBinding default (ann "_1") (BooleDDM.TypeP.expr (fvarTy t1Idx))
  let ctorArgs : Strata.Ann (Option (Strata.Ann (Array (BooleDDM.Binding SourceRange)) SourceRange)) SourceRange :=
    ann (some (ann #[field0, field1]))
  let ctor := BooleDDM.Constructor.constructor_mk default (ann "Tuple_ctor_2") ctorArgs
  let constrList := BooleDDM.ConstructorList.constructorListAtom default ctor
  let dtDecl := BooleDDM.DatatypeDecl.datatype_decl default (ann "Tuple") typeArgs constrList
  pure (.command_datatypes default (ann #[dtDecl]))

/-- Emit `function Seq_lib_zip_with<A, B>(s: Sequence A, t: Sequence B):
    Sequence (Tuple A B);` as an abstract declaration. The return type
    references `Tuple`, so this support decl must be emitted after
    `.tuple`. See `allSupportDecls` ordering in `Support.lean`. -/
private def mkSeqZipWithDecl : BuildM BCmd := do
  let fname := "Seq_lib_zip_with"
  addFreeVars #[fname]
  let typeParamBindings : Array (BooleDDM.TypeVar SourceRange) := #[
    BooleDDM.TypeVar.type_var default (ann "A"),
    BooleDDM.TypeVar.type_var default (ann "B")]
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
    ann (some (BooleDDM.TypeArgs.type_args default (ann typeParamBindings)))
  let aTy := tvarTy "A"
  let bTy := tvarTy "B"
  let tupleIdx ← resolveFreeVar "Tuple"
  let sInput :=
    BooleDDM.Binding.mkBinding default (ann "s") (BooleDDM.TypeP.expr (seqTy aTy))
  let tInput :=
    BooleDDM.Binding.mkBinding default (ann "t") (BooleDDM.TypeP.expr (seqTy bTy))
  let inputBindings :=
    BooleDDM.Bindings.mkBindings default (ann #[sInput, tInput])
  let outputTy : BType := seqTy (fvarTy tupleIdx #[aTy, bTy])
  pure (.command_fndecl default (ann fname) typeArgs inputBindings outputTy)

private def mkArrayFillDecl : BuildM BCmd := do
  let fname := "Array_array_fill_for_copy_types"
  addFreeVars #[fname]
  let typeParamBindings : Array (BooleDDM.TypeVar SourceRange) := #[
    BooleDDM.TypeVar.type_var default (ann "T")]
  let typeArgs : Strata.Ann (Option (BooleDDM.TypeArgs SourceRange)) SourceRange :=
    ann (some (BooleDDM.TypeArgs.type_args default (ann typeParamBindings)))
  let tTy := tvarTy "T"
  let input :=
    BooleDDM.Binding.mkBinding default (ann "value") (BooleDDM.TypeP.expr tTy)
  let inputBindings :=
    BooleDDM.Bindings.mkBindings default (ann #[input])
  let outputTy : BType := mapTy intTy tTy
  pure (.command_fndecl default (ann fname) typeArgs inputBindings outputTy)

def supportDeclToCommand (lowerType : TypeLowerer) (need : SupportDecl) :
    BuildM (Option BCmd) := do
  match need with
  | .tuple => do
    let cmd ← mkTupleDatatypeDecl
    pure (some cmd)
  | .nat => do
    let cmd ← mkAbstractTypeDecl "nat" []
    pure (some cmd)
  | .seqZipWith => do
    let cmd ← mkSeqZipWithDecl
    pure (some cmd)
  | .arrayFill => do
    let cmd ← mkArrayFillDecl
    pure (some cmd)
  | _ =>
    match supportDeclSignature? need with
    | some ([inputTy], outputTy) =>
      let cmd ← mkCastFnDecl lowerType (supportDeclName need) inputTy outputTy
      pure (some cmd)
    | _ => pure none

def supportDeclCommands (lowerType : TypeLowerer) (needs : Array SupportDecl) :
    BuildM (Array BCmd) := do
  let mut cmds : Array BCmd := #[]
  for need in allSupportDecls do
    if needs.any (· == need) then
      match ← supportDeclToCommand lowerType need with
      | some cmd => cmds := cmds.push cmd
      | none => pure ()
  pure cmds

end VerusLean.Boole.SupportEmit
