import Lean
import VerusLean
import VerusLean.VLIR.Boole.Translate
import VerusLean.VLIR.Boole.Emit
import VerusLean.VLIR.Boole.Prelude

open VerusLean
open VerusLean.Boole

/-- Text preludes keep source comments for maintainability, but generated
    output files should stay concise. Drop standalone `// ...` lines before
    prepending the prelude text. -/
private def stripLineComments (text : String) : String :=
  String.intercalate "\n" <|
    (text.splitOn "\n").filter (fun line =>
      let trimmed := line.trimAscii.toString
      !trimmed.startsWith "//")

/-- Read a Boole prelude file relative to the `verus-boogie` repo root. -/
private def readPreludeBody? (fileName : String) : IO (Option String) := do
  let cwd ← IO.currentDir
  let path := cwd / "prelude" / fileName
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    pure <| some <| stripLineComments text
  else
    pure none

private def readSeqPreludeBody? : IO (Option String) :=
  readPreludeBody? "Seq.boole.st"

private def readVecPreludeBody? : IO (Option String) :=
  readPreludeBody? "Vec.boole.st"

private def assemblePreludeText
    (seqNeeded vecNeeded : Bool)
    (seqPreludeBody? vecPreludeBody? : Option String) : Option String :=
  let pieces :=
    [if seqNeeded then seqPreludeBody? else none, if vecNeeded then vecPreludeBody? else none]
      |>.filterMap id
  match pieces with
  | [] => none
  | _ => some (String.intercalate "\n\n" pieces)

private def failWith (msg : String) : IO α :=
  throw <| IO.userError s!"Error: {msg}"

private def collectJsonBundleFiles (target : System.FilePath) : IO (List System.FilePath) := do
  match target.fileStem, target.extension with
  | some stem, some "json" => do
    let dir := target.parent.getD (System.FilePath.mk ".")
    let shardPrefix := s!"{stem}_"
    let entries ← dir.readDir
    let shards :=
      entries.foldl (init := ([] : List System.FilePath)) (fun acc entry =>
        if entry.fileName.startsWith shardPrefix && entry.fileName.endsWith ".json" then
          entry.path :: acc
        else
          acc)
    let sortedShards := (shards.toArray.qsort (fun a b => a.toString < b.toString)).toList
    pure (target :: sortedShards)
  | _, _ => pure [target]

private def booleCommandRank (cmd : Boole.Builder.BCmd) : Nat :=
  match cmd with
  | .command_fndef .. => 2
  | .boole_procedure _ _ _ _ _ _ bodyAnn => if bodyAnn.val.isSome then 2 else 1
  | .command_procedure _ _ _ _ _ bodyAnn => if bodyAnn.val.isSome then 2 else 1
  | .command_typedecl .. => 2
  | .command_typesynonym .. => 2
  | .command_datatypes .. => 2
  | _ => 1

private def maxRankForName (cmds : List Boole.Builder.BCmd) (name : String) : Nat :=
  cmds.foldl (init := 0) fun acc cmd =>
    if Translate.cmdDeclName? cmd == some name then
      Nat.max acc (booleCommandRank cmd)
    else
      acc

/-- Module shards can contain both an imported declaration and the defining
    body for the same symbol. Keep one named command, preferring definitions
    over declarations, before building a Strata global context. -/
private def dedupeNamedCommands (cmds : Array Boole.Builder.BCmd) :
    Array Boole.Builder.BCmd :=
  let all := cmds.toList
  let rec go (seen : List String) : List Boole.Builder.BCmd → List Boole.Builder.BCmd
    | [] => []
    | cmd :: rest =>
        match Translate.cmdDeclName? cmd with
        | none => cmd :: go seen rest
        | some name =>
            let bestRank := maxRankForName all name
            if booleCommandRank cmd == bestRank && !seen.contains name then
              cmd :: go (name :: seen) rest
            else
              go seen rest
  (go [] all).toArray

unsafe def genBooleFromFile
    (path : String)
    (printFn : String → IO Unit) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let seqPreludeBody? ← readSeqPreludeBody?
  let vecPreludeBody? ← readVecPreludeBody?
  let mut allDecls : List Decl := []
  for f in bundleFiles do
    match ← Decls.fromFile? f.toString with
    | .ok (_ns, defs, thms, _callTypes) =>
      allDecls := allDecls ++ defs ++ thms
    | .error e =>
      if f == target then failWith e
      else IO.eprintln s!"warning: skipping shard {f}: {e}"
  -- Plan prelude loading from VLIR syntax before BooleDDM construction, then
  -- translate once with the parsed prelude names pre-registered so fvar
  -- indices align with Strata's global context.
  let preludePlan := Boole.Prelude.planDecls allDecls
  let preludeText? := assemblePreludeText
      (preludePlan.needsSeq && seqPreludeBody?.isSome)
      (preludePlan.needsVec && vecPreludeBody?.isSome)
      seqPreludeBody? vecPreludeBody?
  let preludeResult ←
    match preludeText? with
    | some text => Boole.Emit.loadPrelude text
    | none => pure (.ok (#[], #[]))
  match preludeResult with
  | .error e => failWith e
  | .ok (preludeOps, preludeNames) =>
    match Translate.translateDeclsWithPrelude allDecls preludeNames with
    | .error e => failWith e
    | .ok (cmds, finalCtx) =>
      -- Filter out user commands whose names are already in the prelude
      let preludeSet := preludeNames.toList
      let cmds := cmds.filter fun cmd =>
        match Translate.cmdDeclName? cmd with
        | some name => !preludeSet.contains name
        | none => true
      let cmds := dedupeNamedCommands cmds
      let bodyOps := Boole.Emit.commandsToOps cmds
      -- Use Strata's official Boole.formatProgram with explicit GlobalContext
      match Boole.Emit.renderProgram preludeOps bodyOps finalCtx.allFreeVars with
      | .ok output => printFn output
      | .error e => failWith e

unsafe def main : List String → IO Unit
  | ["boole", path] => genBooleFromFile path IO.println
  | ["boole", path, toFile] => genBooleFromFile path (IO.FS.writeFile toFile)
  | [path] => genBooleFromFile path IO.println
  | [path, toFile] => genBooleFromFile path (IO.FS.writeFile toFile)
  | _ =>
    IO.println "Usage: ./verus-lean [boole] <input.json> [output.boole.st]"
