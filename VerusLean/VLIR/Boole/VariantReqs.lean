/-
  Boole.VariantReqs — VLIR analysis for synthesised variant preconditions.

  Verus's `self->Variant.field` accessor sugar lowers to a partial spec
  fn whose body is a bare `.Unary (.Proj dt variant field _ check:None)`,
  with the partiality (the implicit "self is Variant" obligation)
  recorded only on the destructor — not on the spec fn itself. To keep
  Strata happy we reconstruct the obligation by walking the spec-fn
  body, finding every `.Proj` applied directly to a named parameter,
  and emitting a `requires <dt>..is<variant>(<param>)` precondition.

  This module owns the *analysis* (which Projs warrant a precondition).
  The actual emission (`synthVariantRequires`) is BuildM-valued and
  stays alongside `specFnToBoole` in `Translate.lean`.
-/
import VerusLean.VLIR.Defs

namespace VerusLean.Boole.VariantReqs

open VerusLean

/-- Peel `Box`/`Unbox`/`Decorated` wrappers to find an underlying `.Var` name,
    if any. Used to decide whether a `.Proj` is being applied directly to a
    named parameter (and thus needs a caller-supplied variant precondition). -/
partial def unwrapToVar : Exp → Option String
  | .Var x => some x
  | .Unary (.Box _) e | .Unary (.Unbox _) e => unwrapToVar e
  | _ => none

/-- Collect `(paramName, dt, variant)` triples for every `.Proj` appearing on
    the *root* path of the body — i.e. not under any control-flow node
    (`.If`/`.Bind`/`.MatchBlock`/etc.) which would already constrain the
    variant via a surrounding guard.

    Used by spec-fn translation to synthesise `requires <dt>..is<variant>(x)`
    preconditions for Verus's inline accessor sugar (`self->Variant.field`),
    which Verus encodes as `.Unary (.Proj dt variant field _ check:None)`
    without recording the partiality on the function. Without this, Strata
    correctly flags the implicit variant precondition of the datatype
    destructor as an unprovable obligation inside every such function body. -/
partial def rootExposedProjs : Exp → List (String × Ident × String)
  | .Unary (.Proj dt variant _ _ _) arg =>
    let here := match unwrapToVar arg with
      | some name => [(name, dt, variant)]
      | none => []
    here ++ rootExposedProjs arg
  | .Unary _ arg => rootExposedProjs arg
  | .Binary _ a b => rootExposedProjs a ++ rootExposedProjs b
  | _ => []

def dedupVariantReqs (xs : List (String × Ident × String)) :
    List (String × Ident × String) :=
  xs.foldl (fun acc t => if acc.contains t then acc else acc ++ [t]) []

end VerusLean.Boole.VariantReqs
