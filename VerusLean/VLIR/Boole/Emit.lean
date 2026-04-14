/-
  Boole.Emit — Assemble BooleDDM commands into a Strata.Program and emit text.

  This module owns the final step:  `Array BooleDDM.Command → String`.
  It handles:
    • Name resolution context (ToCSTContext) for free/bound variable indices.
    • Prelude text loading + merging.
    • Calling Strata's official formatter (`Boole.formatProgram`).
-/
import VerusLean.VLIR.Boole.Builder

import Strata.Languages.Boole.Boole
import Strata.Languages.Boole.Verify
import Strata.Languages.Core.DDMTransform.ASTtoCST
import Strata.Util.IO

namespace VerusLean.Boole.Emit

open Strata
open Strata.BooleDDM
open VerusLean.Boole.Builder

/-- The build context tracks free/bound variable scopes for de Bruijn index
    resolution when constructing BooleDDM nodes. -/
abbrev BuildCtx := ToCSTContext SourceRange
abbrev BuildM := StateT BuildCtx (Except String)

def emptyCtx : BuildCtx := ToCSTContext.empty

/-- Run a sub-computation in a fresh scope (pushes and pops). -/
def withScope (k : BuildM α) : BuildM α := do
  modify ToCSTContext.pushScope
  try
    let out ← k
    modify ToCSTContext.popScope
    pure out
  catch e =>
    modify ToCSTContext.popScope
    throw e

/-- Add names as bound variables in the current scope.

    Boole verification resolves bvar index 0 to the newest/rightmost binder.
    Keep binders in source order here and make lookup search from the right;
    this preserves source binder order while producing verifier-compatible
    de Bruijn indices. -/
def addBoundVars (names : Array String) (reverse? : Bool := false) : BuildM Unit := do
  let names := if reverse? then names.reverse else names
  modify fun ctx =>
    let idx := ctx.scopes.size - 1
    let scope := ctx.scopes[idx]!
    let newScope := { scope with boundVars := scope.boundVars ++ names }
    { ctx with scopes := ctx.scopes.set! idx newScope }

/-- Push a single bound var to current scope (convenience for init stmts). -/
def pushBoundVar (name : String) : BuildM Unit :=
  modify (·.pushBoundVar name)

/-- Register names as global free variables (skip already-registered). -/
def addFreeVars (names : Array String) : BuildM Unit := do
  let ctx ← get
  let fresh := names.filter (fun name => ctx.freeVarIndex? name |>.isNone)
  modify (·.addGlobalFreeVars fresh)

/-- Look up the free variable index for a name, registering it if new. -/
def resolveFreeVar (name : String) : BuildM Nat := do
  addFreeVars #[name]
  let ctx ← get
  match ctx.freeVarIndex? name with
  | some idx => pure idx
  | none => throw s!"bug: failed to register free variable '{name}'"

/-- Find the de Bruijn index of the rightmost matching binder.

    This handles ordinary shadowing correctly: inner scopes are appended after
    outer scopes, and later declarations in the same binder list are newer. -/
private def findBoundVarIndex? (vars : Array String) (name : String) : Option Nat :=
  let rec go (remaining : Nat) (offset : Nat) : Option Nat :=
    match remaining with
    | 0 => none
    | i + 1 =>
        if vars[i]! == name then
          some offset
        else
          go i (offset + 1)
  go vars.size 0

/-- Look up a bound variable by name. Returns `none` if not in scope. -/
def lookupBoundVar (name : String) : BuildM (Option Nat) := do
  let ctx ← get
  pure (findBoundVarIndex? ctx.allBoundVars name)

/-- Convert an array of BooleDDM Commands to Strata Operations. -/
def commandsToOps (cmds : Array BCmd) : Array Strata.Operation :=
  cmds.map (·.toAst)

/-- Loaded dialect map for Boole. -/
private def loadedBooleDialects : Strata.Elab.LoadedDialects :=
  Strata.Elab.LoadedDialects.ofDialects! Strata.Boole_map.toList.toArray

/-- Parse Boole text into a Strata.Program (for prelude loading). -/
def parseBooleText (text : String) : IO (Except String Strata.Program) := do
  let fm ← Strata.DialectFileMap.new loadedBooleDialects
  match ← Strata.Util.readStrataText fm "<generated-boole>" text.toUTF8 with
  | .program pgm => pure (.ok pgm)
  | .dialect _ => pure (.error "expected a Boole program, but Strata parsed a dialect")

/-- Load prelude text, parse it, and return its operations + global names. -/
def loadPrelude (preludeText : String) :
    IO (Except String (Array Strata.Operation × Array String)) := do
  match ← parseBooleText s!"program Boole;\n\n{preludeText.trimAsciiEnd.toString}\n" with
  | .ok pgm =>
    pure (.ok (pgm.commands, pgm.globalContext.vars.map (·.1)))
  | .error e => pure (.error e)

/-- Build a `GlobalContext` from a list of names, in order. Uses
    `GlobalKind.type [] none` as a placeholder kind; the formatter only looks
    up names by index, not by kind. -/
def buildGlobalContext (names : Array String) : Strata.GlobalContext :=
  names.foldl (fun ctx name =>
    ctx.ensureDefined name (.type [] none)) {}

/-- Render Boole commands to text using Strata's `Boole.formatProgram` with an
    explicit `GlobalContext`. This uses the PR fix to resolve fvar indices when
    commands come from `BooleDDM.toAst` (which doesn't populate globalContext).

    `preludeOps` are the parsed prelude's operations (or empty).
    `bodyOps` are our translated commands as operations.
    `freeVarNames` is the ordered list of names in our `BuildCtx.allFreeVars`
    — used to construct the `GlobalContext` for Strata's formatter. -/
def renderProgram
    (preludeOps bodyOps : Array Strata.Operation)
    (freeVarNames : Array String) : Except String String :=
  let allOps := preludeOps ++ bodyOps
  let pgm := Strata.Program.create Strata.Boole_map "Boole" allOps
  match Strata.Boole.getProgram pgm with
  | .error e => .error (toString e)
  | .ok booleProg =>
    let gctx := buildGlobalContext freeVarNames
    let formatted := Strata.Boole.formatProgram booleProg gctx Strata.Boole_map
    let body := Std.Format.pretty formatted 100
    -- `Boole.formatProgram` emits only the program body; the dialect header
    -- is required for the output to be re-parseable (this mirrors the fix
    -- Strata PR #767 applied to `Core.formatProgram` for `program Core;`).
    let output := s!"program Boole;\n\n{body}"
    let output := if output.endsWith "\n" then output else output ++ "\n"
    .ok output

end VerusLean.Boole.Emit
