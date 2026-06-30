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

/-- Locate `prelude/<fileName>` by walking up from `start` (bounded), so the
    prelude is found whether `verus-lean` runs from the repo root or a subdir. -/
private def searchUpForPrelude
    (start : System.FilePath) (fileName : String) : IO (Option System.FilePath) := do
  let mut dir := start
  for _ in [0:16] do
    let cand := dir / "prelude" / fileName
    if ← cand.pathExists then
      return some cand
    match dir.parent with
    | some p => dir := p
    | none => return none
  return none

/-- Read a Boole prelude file.  Resolves `prelude/<fileName>` robustly — first by
    walking up from the current directory, then from the running binary's
    location — so a generated `.boole.st` is self-contained (the `nat` prelude it
    references is defined) regardless of the invocation cwd. -/
private def readPreludeBody? (fileName : String) : IO (Option String) := do
  let path? ←
    match ← searchUpForPrelude (← IO.currentDir) fileName with
    | some p => pure (some p)
    | none =>
      match (← IO.appPath).parent with
      | some binDir => searchUpForPrelude binDir fileName
      | none => pure none
  match path? with
  | some path =>
    let text ← IO.FS.readFile path
    pure <| some <| stripLineComments text
  | none =>
    pure none

private def readNatPreludeBody? : IO (Option String) :=
  readPreludeBody? "Nat.boole.st"

private def readSeqPreludeBody? : IO (Option String) :=
  readPreludeBody? "Seq.boole.st"

private def readVecPreludeBody? : IO (Option String) :=
  readPreludeBody? "Vec.boole.st"

/-- True iff `nat` appears as a whole identifier token in `s` — the Boole `nat`
    type, or the `nat` head of a `nat.toInt` / `nat.add` / … call (`.` is a token
    separator).  Tokenizes on identifier boundaries so substrings like `nation`
    do not match.  Used to decide, from the actually-rendered program text,
    whether the `nat` prelude is referenced. -/
private def referencesNatToken (s : String) : Bool :=
  let isIdent := fun (c : Char) => c.isAlphanum || c == '_'
  let (found, lastTok) := s.foldl (init := ((false, "") : Bool × String))
    (fun (found, cur) c =>
      if isIdent c then (found, cur.push c)
      else (found || cur == "nat", ""))
  found || lastTok == "nat"

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
  | .boole_procedure _ _ _ _ _ _ _ bodyAnn => if bodyAnn.val.isSome then 2 else 1
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

/-- Build the synthesized-aid toggle config from the `BOOLE_SYNTH_DISABLE`
    environment variable — a comma-separated list of `SynthConfig` field names
    to turn *off* (e.g. `fixedArrayLengths,loopLowerBound,seqMapPrecond`).
    Empty/unset means all aids on (the default).  Unknown names are ignored. -/
def synthConfigFromEnv : IO Context.SynthConfig := do
  let raw := (← IO.getEnv "BOOLE_SYNTH_DISABLE").getD ""
  let off := (raw.splitOn ",").map (·.trim) |>.filter (· != "")
  pure {
    fixedArrayLengths := !off.contains "fixedArrayLengths"
    loopLowerBound    := !off.contains "loopLowerBound"
    seqMapPrecond     := !off.contains "seqMapPrecond"
  }

unsafe def genBooleFromFile
    (path : String)
    (printFn : String → IO Unit) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let natPreludeBody? ← readNatPreludeBody?
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
  let synthCfg ← synthConfigFromEnv
  let preludePlan := Boole.Prelude.planDecls allDecls
  -- Load each prelude piece separately so the `nat` block can be dropped when
  -- the emitted program never references it.  `nat`'s names are registered
  -- (loaded) whenever the file is present, keeping fvar indices stable; whether
  -- the `nat` declarations are *emitted* is decided post-translation from the
  -- rendered text.  Seq/Vec gate on their VLIR triggers.
  let loadPiece (needed : Bool) (body? : Option String) := do
    if needed then
      match body? with
      | some text =>
        match ← Boole.Emit.loadPrelude text with
        | .ok r => pure r
        | .error e => failWith e
      | none => pure (#[], #[])
    else pure (#[], #[])
  let (natOps, natNames) ← loadPiece natPreludeBody?.isSome natPreludeBody?
  let (seqOps, seqNames) ← loadPiece (preludePlan.needsSeq && seqPreludeBody?.isSome) seqPreludeBody?
  let (vecOps, vecNames) ← loadPiece (preludePlan.needsVec && vecPreludeBody?.isSome) vecPreludeBody?
  -- Order matters: Nat first — Seq bodies reference `int_to_nat` from Nat.
  let preludeNames := natNames ++ seqNames ++ vecNames
  match Translate.translateDeclsWithPrelude allDecls preludeNames synthCfg with
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
    -- Emit the `nat` prelude only when the rest of the program — the body plus
    -- the Seq/Vec prelude pieces, whose bodies reference `nat` — actually names a
    -- `nat` token.  Decided from the rendered text, so an over-approximating
    -- trigger (e.g. a native `Sequence` ref tripping `needsSeq`) never forces a
    -- dead prelude.  On a render error, keep `nat` (matches always-emit behavior).
    let natNeeded :=
      match Boole.Emit.renderProgram (seqOps ++ vecOps) bodyOps finalCtx.allFreeVars with
      | .ok text => referencesNatToken text
      | .error _ => true
    let preludeOps := (if natNeeded then natOps else #[]) ++ seqOps ++ vecOps
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
