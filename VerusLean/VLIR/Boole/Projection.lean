/-
  Boole.Projection — Datatype field-name layout for projected
  assignments and reads.

  Verus's `s.field = rhs` (struct/enum field assignment) lowers to a
  reconstruction: rebuild the parent struct/enum value with the new
  field substituted in, then assign that back to the root variable.
  To do that we need a per-datatype layout describing each variant's
  constructor name and field-name list — exactly what `ProjLayout`
  records.

  This module owns the layout-building / layout-querying side of that
  analysis. The BuildM-bound consumers (`lvalueReadExprToBoole`,
  `lowerProjectedAssignRhsToRoot`) stay alongside `stmToBoole` in
  `Translate.lean` because they emit BooleDDM constructor calls.

  Pure: no `BuildM`, no BooleDDM emission. Just `Decl` / `LValue`
  inspection.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.Projection

open VerusLean
open VerusLean.Boole.Names

/-- Per-variant layout: the constructor name to rebuild with, plus the
    canonical field-name list (struct field names for structs;
    `<dt>..<variant>_<field>` accessor names for enum variants). -/
structure ProjLayout where
  dt : Ident
  variant : String
  ctorName : String
  fields : List String
  isEnum : Bool

def projLayoutsFromDecl : Decl → List ProjLayout
  | .struct s =>
    [{ dt := s.name
       variant := datatypeNameOf s.name
       ctorName := structCtorNameOf s.name
       fields := s.fields.map Prod.fst
       isEnum := false }]
  | .enum e =>
    e.fields.map (fun field =>
      match field with
      | .labeled variant data =>
        { dt := e.name, variant := variant
          ctorName := enumCtorNameOf e.name variant
          fields := data.map (fun (fname, _) => projFieldNameOf e.name variant fname)
          isEnum := true }
      | .tuple variant ts =>
        { dt := e.name, variant := variant
          ctorName := enumCtorNameOf e.name variant
          fields := (List.range ts.length).map (fun i => projFieldNameOf e.name variant (toString i))
          isEnum := true })
  | .mutualBlock ds => ds.flatMap projLayoutsFromDecl
  | _ => []

def buildProjLayouts (decls : List Decl) : List ProjLayout :=
  decls.flatMap projLayoutsFromDecl

/-- Find the `ProjLayout` for `dt::variant`. Struct lookups ignore the
    variant slot; enum lookups match on sanitised variant name. -/
def findProjLayout? (layouts : List ProjLayout) (dt : Ident) (variant : String) :
    Option ProjLayout :=
  let dtName := datatypeNameOf dt
  let variantName := sanitizeIdent variant
  layouts.find? (fun l =>
    datatypeNameOf l.dt == dtName &&
      if l.isEnum then sanitizeIdent l.variant == variantName else true)

/-- Resolve a source field name to whichever spelling actually appears
    in the layout's field list. Verus emits projection-field names
    inconsistently across `.Proj` sites (raw name, sanitised name,
    `<dt>..<variant>_<field>`, `<dt>..<dt>_<field>` for structs); this
    walks the candidate list and returns the first match. -/
def resolveProjFieldName? (layout : ProjLayout) (dt : Ident) (variant field : String) :
    Option String :=
  let candidates :=
    ([field, sanitizeIdent field,
      projFieldNameOf dt variant field,
      projFieldNameOf dt (datatypeNameOf dt) field]).eraseDups
  candidates.find? (fun c => layout.fields.contains c)

/-- Lift an `LValue` to the equivalent `Exp` for read-side use. Used by
    `lvalueReadExprToBoole` (which then translates the resulting
    `Exp`) and by `lowerProjectedAssignRhsToRoot` to construct the
    container expression for the rebuild step. -/
def lvalueToExp : LValue → Exp
  | .Var name => .Var name
  | .Proj base dt variant field getVariant check =>
    .Unary (.Proj dt variant field getVariant check) (lvalueToExp base)
  | .Proj' base size field =>
    .Unary (.Proj' size field) (lvalueToExp base)
  | .Index base index =>
    .Binary .Index (lvalueToExp base) index

end VerusLean.Boole.Projection
