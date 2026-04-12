import Lean
import VerusLean
import VerusLean.VLIR.Translate
import VerusLean.VLIR.Boole.Emit

open VerusLean

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

/-- Names provided by the Seq prelude file. Declarations with these names
    are filtered out of the translator output to avoid duplicates. -/
private def seqPreludeProvidedNames : List String :=
  ["nat", "int_to_nat", "Set", "Set_finite",
   "Seq_len", "Seq_lib_insert", "Seq_new", "Seq_lib_map",
   "Seq_lib_map_values", "Seq_lib_filter", "Seq_lib_sort_by",
   "Seq_lib_to_set"]

/-- Names provided by the Vec prelude file. -/
private def vecPreludeProvidedNames : List String :=
  ["Vec", "Vec_ctor", "Vec_data", "Vec_len", "Vec_index", "Vec_view"]

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
  match Translate.translateDecls allDecls with
  | .error e => failWith e
  | .ok cmds =>
    let preludeText? := assemblePreludeText seqPreludeBody?.isSome vecPreludeBody?.isSome
        seqPreludeBody? vecPreludeBody?
    let preludeProvides : List String :=
      (if seqPreludeBody?.isSome then seqPreludeProvidedNames else []) ++
      (if vecPreludeBody?.isSome then vecPreludeProvidedNames else [])
    let cmds := cmds.filter fun cmd =>
      match Translate.cmdDeclName? cmd with
      | some name => !preludeProvides.contains name
      | none => true
    let preludeResult ←
      match preludeText? with
      | some text => Boole.Emit.loadPrelude text
      | none => pure (.ok (#[], #[]))
    match preludeResult with
    | .error e => failWith e
    | .ok (preludeOps, _) =>
      let bodyOps := Boole.Emit.commandsToOps cmds
      let pgm := Boole.Emit.mkProgram preludeOps bodyOps
      printFn (Boole.Emit.programToString pgm)

unsafe def main : List String → IO Unit
  | ["boole", path] => genBooleFromFile path IO.println
  | ["boole", path, toFile] => genBooleFromFile path (IO.FS.writeFile toFile)
  | [path] => genBooleFromFile path IO.println
  | [path, toFile] => genBooleFromFile path (IO.FS.writeFile toFile)
  | _ =>
    IO.println "Usage: ./verus-lean [boole] <input.json> [output.boole.st]"
