/-
  Boole.Emit — Assemble BooleDDM commands into a Strata.Program and emit text.

  This module owns the final step:  `Array BooleDDM.Command → String`.
  It handles:
    • Name resolution context (ToCSTContext) for free/bound variable indices.
    • Prelude text loading + merging.
    • Calling Strata's official formatter (`Program.toString`).
-/
import VerusLean.VLIR.Boole.Builder

import Strata.Languages.Boole.Boole
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

private def ann (v : α) : Strata.Ann α SourceRange := ⟨default, v⟩

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

/-- Add names as bound variables in the current scope. -/
def addBoundVars (names : Array String) (reverse? : Bool := false) : BuildM Unit :=
  modify (ToCSTContext.addScopedBoundVars · names (reverse? := reverse?))

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

/-- Look up a bound variable by name. Returns `none` if not in scope. -/
def lookupBoundVar (name : String) : BuildM (Option Nat) := do
  let ctx ← get
  pure (ctx.findBoundVarIndex? name)

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

/-- Create a `Strata.Program` from operations (prelude + body). -/
def mkProgram (preludeOps bodyOps : Array Strata.Operation) : Strata.Program :=
  Strata.Program.create Strata.Boole_map "Boole" (preludeOps ++ bodyOps)

/-- Render a program to Boole text. -/
def programToString (pgm : Strata.Program) : String :=
  let output := pgm.toString
  if output.endsWith "\n" then output else output ++ "\n"

end VerusLean.Boole.Emit
