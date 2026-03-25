import Lean
import Lean.PrettyPrinter
import VerusLean
import VerusLean.VLIR.ToCore
import Strata.Languages.Core.DDMTransform.ASTtoCST

open VerusLean

open Lean PrettyPrinter
open VName

/-- Strip the standard `program Core;\n\n` header so we can prepend another
    textual prelude without duplicating the program header. -/
private def stripCoreProgramHeader (text : String) : String :=
  let header := "program Core;\n\n"
  if text.startsWith header then
    (text.drop header.length).toString
  else
    text

/-- The Seq prelude keeps source comments for maintainability, but generated
    `.core.st` files should stay concise. Drop standalone `// ...` lines before
    prepending the prelude text. -/
private def stripLineComments (text : String) : String :=
  String.intercalate "\n" <|
    (text.splitOn "\n").filter (fun line =>
      let trimmed := line.trimAscii.toString
      !trimmed.startsWith "//")

/-- Read `prelude/Seq.core.st` relative to the `verus-boogie` repo root.
    If the file is absent, translation still proceeds without textual prelude
    insertion and falls back to internal typed stubs. -/
private def readSeqPreludeBody? : IO (Option String) := do
  let cwd ← IO.currentDir
  let path := cwd / "prelude" / "Seq.core.st"
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    pure <| some <| stripLineComments (stripCoreProgramHeader text)
  else
    pure none

/-- Prepend the textual Seq prelude while keeping exactly one `program Core;`
    header in the final output. -/
private def prependSeqPrelude (prelude body : String) : String :=
  s!"program Core;\n\n{prelude.trimAsciiEnd.toString}\n\n{stripCoreProgramHeader body}"

/-
def genFromDir (dirPath : String) : IO String := do
  -- For each file in the directory
  let files ← System.FilePath.walkDir dirPath
  let (str, _) ← files.foldlM (init := ("", 1)) (fun (str, counter) entry => do
    -- Get out the filepath in the entry, open it, and run `genFromFile`
    let res ← Exp.fromFile? entry.toString
    match res with
    | .ok (e, map) =>
      let declsString := map.fold (init := "") (fun str k v => str ++ s!"({k} : {v.toSyntax}) ")
      let str := str ++ e.toTheoremString (name := s!"verus_thm_{counter}") (decls := declsString)
      return (str, counter + 1)
    | .error _ => do
      -- TODO: Error handling?
      let str := str ++ s!"-- The JSON at {entry} failed to generate\n\n"
      return (str, counter)
  )

  return str -/

/-
unsafe def genFromDir' (dirPath : String) : IO String := do
  -- Get all the files in the requested directory
  let files ← System.FilePath.walkDir dirPath

  /-
    Currently, each assertion (filename) is tagged with an increasing ID.
    Later assertions may depend on earlier spec functions or assertions.

    TODO: Place all asserts into one file? Use something other than IDs?
  -/
  let files := files.insertionSort (fun a b =>
    let a := a.toString
    let b := b.toString
    if a.length < b.length then true
    else if a.length > b.length then false
    else a < b)

  -- Accumulate the function map, assertions, and proof functions across all files
  -- Store serializations that fail to parse as error strings
  -- We use an `Array` for `Assertion`s because `push` is O(1) for arrays
  let (fmap, dtmap, asserts, prooffns, failures) ← files.foldlM (init := ((∅, ∅, #[], #[], "") : FnMap × DeclMap × Array Assertion × Array FuncCheckSst × String))
    (fun (fnmap, dtmap, as, ps, str) filePath => do
    match ← Decls.fromFile? filePath.toString with
    -- CC TODO: Ignoring the namespace here...
    | .ok (_, ds) => do
      let ⟨fnmap, dtmap, as, ps⟩ ←
        ds.foldlM (init := (fnmap, dtmap, as, ps)) (fun (fnmap, dtmap, as, ps) decl => do
          match decl with
          | .specFn f => return (fnmap.insert (name f) f, dtmap, as, ps)
          | .proofFn f => return (fnmap, dtmap, as, ps) -- CC TODO This is broken
          | .struct s => return (fnmap, dtmap.insert (name s) s, as, ps)
          | .enum e => return (fnmap, dtmap.insert (name e) e, as, ps)
          | .assertion a => return (fnmap, dtmap, as.push a, ps)
          | .func f => return (fnmap, dtmap, as, ps.push f))
      return (fnmap, dtmap, as, ps, str)
    | .error e => do
      dbg_trace e
      return (fnmap, dtmap, as, ps, str ++ s!"-- The JSON at {filePath} failed to generate\n\n")
  )

  let decls := dtmap.values
               ++ fmap.values.map (Decl.specFn ·)
               ++ asserts.toList.map (Decl.assertion ·)
               ++ prooffns.toList.map (Decl.func ·)

  match ← Decl.toFormat "VL" decls with
  | .ok s => return s ++ failures
  | .error e => return s!"Error: {e}" -/

unsafe def genFromFile (path : String) (printFn : String → IO Unit) : IO Unit := do
  match ← Decls.fromFile? path with
  | .ok (ns, defs, thms, _callTypes) =>
    match ← Decl.toFormat ns defs thms with
    | .ok str => printFn str
    | .error e => IO.println s!"Error: {e}"
  | .error e => IO.println e

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
    -- Translate the requested JSON plus same-stem module shards (`base_*.json`).
    pure (target :: sortedShards)
  | _, _ => pure [target]

unsafe def genCoreFromFile (path : String) (printFn : String → IO Unit)
    (useOfficialPrinter : Bool := false) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let seqPreludeBody? ← readSeqPreludeBody?
  let mut allDecls : List Decl := []
  let mut allCallSiteTypes : CallSiteTypes := {}
  for f in bundleFiles do
    match ← Decls.fromFile? f.toString with
    | .ok (_ns, defs, thms, callTypes) =>
      allDecls := allDecls ++ defs ++ thms
      -- Merge call-site type signatures, keeping the first seen for each name.
      for (name, sig) in callTypes.toList do
        if !allCallSiteTypes.contains name then
          allCallSiteTypes := allCallSiteTypes.insert name sig
    | .error e =>
      if f == target then
        -- Primary file failure is fatal.
        IO.println e
        return ()
      else
        -- Keep translating other shards so one unsupported module does not block output.
        IO.eprintln s!"warning: skipping shard {f}: {e}"
  match ToCore.declsToProgram allDecls allCallSiteTypes (useTextSeqPrelude := seqPreludeBody?.isSome) with
  | .ok (p, fnDecMap, seqPreludeNeeded) =>
    if useOfficialPrinter then
      -- Use Strata's official DDM-based pretty-printer (Core.formatProgram).
      -- Note: output does not include the "program Core;" header.
      let formatted := Std.Format.pretty (Strata.Core.formatProgram p) 100
      let output :=
        match seqPreludeNeeded, seqPreludeBody? with
        | true, some prelude => prependSeqPrelude prelude (formatted ++ "\n")
        | _, _ => "program Core;\n\n" ++ formatted ++ "\n"
      printFn output
    else
      let body := ToCore.Pretty.programToString p fnDecMap
      let output :=
        match seqPreludeNeeded, seqPreludeBody? with
        | true, some prelude => prependSeqPrelude prelude body
        | _, _ => body
      printFn output
  | .error e => IO.println s!"Error: {e}"

unsafe def main : List String → IO Unit
  | [path] => genFromFile path IO.println
  | ["boogie", path] => genCoreFromFile path IO.println
  | ["boogie", path, toFile] => genCoreFromFile path (IO.FS.writeFile toFile)
  | ["core", "--official", path] => genCoreFromFile path IO.println (useOfficialPrinter := true)
  | ["core", "--official", path, toFile] =>
    genCoreFromFile path (IO.FS.writeFile toFile) (useOfficialPrinter := true)
  | ["core", path] => genCoreFromFile path IO.println
  | ["core", path, toFile] => genCoreFromFile path (IO.FS.writeFile toFile)
  /-| ["dir", path] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.println <| preludeString "hello" ++ res ++ postludeString "hello" -/

  | [path, toFile] => genFromFile path (IO.FS.writeFile toFile)

  /-| ["dir", path, toFile] => do
    -- IO.println "Reading from a directory"
    let res ← genFromDir' path
    IO.FS.writeFile toFile (preludeString "hello" ++ res ++ postludeString "hello") -/

  | _ =>
    IO.println "Usage: ./verus-lean <input.json> [output.lean]\n\
      ./verus-lean boogie <input.json> [output.core.st]\n\
      ./verus-lean core [--official] <input.json> [output.core.st]"
