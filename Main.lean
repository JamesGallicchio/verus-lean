import Lean
import Lean.PrettyPrinter
import VerusLean
import VerusLean.VLIR.ToCore
import VerusLean.VLIR.OutputPrep
import VerusLean.VLIR.Pretty
import VerusLean.VLIR.Boole.CoreToBoole
import Strata.Languages.Core.DDMTransform.ASTtoCST

open VerusLean

open Lean PrettyPrinter
open VName

/-- The local pretty-printer emits a fixed program header per dialect.
    Strip it before prepending a textual prelude so the final file keeps
    exactly one header. -/
private def stripProgramHeader (dialect : ToCore.OutputDialect) (text : String) : String :=
  let header :=
    match dialect with
    | .core => "program Core;\n\n"
    | .boole => "program Boole;\n\n"
  if text.startsWith header then
    (text.drop header.length).toString
  else
    text

private def programHeader (dialect : ToCore.OutputDialect) : String :=
  match dialect with
  | .core => "program Core;"
  | .boole => "program Boole;"

/-- Text preludes keep source comments for maintainability, but generated
    output files should stay concise. Drop standalone `// ...` lines before
    prepending the prelude text. -/
private def stripLineComments (text : String) : String :=
  String.intercalate "\n" <|
    (text.splitOn "\n").filter (fun line =>
      let trimmed := line.trimAscii.toString
      !trimmed.startsWith "//")

/-- Read a textual prelude relative to the `verus-boogie` repo root.
    The file itself is written in Core concrete syntax, so strip the Core
    header before reusing it in either Core or Boole output. -/
private def readPreludeBody? (fileName : String) : IO (Option String) := do
  let cwd ← IO.currentDir
  let path := cwd / "prelude" / fileName
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    pure <| some <| stripLineComments (stripProgramHeader .core text)
  else
    pure none

private def readSeqPreludeBody? : IO (Option String) :=
  readPreludeBody? "Seq.core.st"

private def readVecPreludeBody? : IO (Option String) :=
  readPreludeBody? "Vec.core.st"

private def prependPrelude (dialect : ToCore.OutputDialect) (prelude body : String) : String :=
  s!"{programHeader dialect}\n\n{prelude.trimAsciiEnd.toString}\n\n{stripProgramHeader dialect body}"

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

private def parseOutputDialect? : String → Option ToCore.OutputDialect
  | "core" => some .core
  | "boole" => some .boole
  | _ => none

private def parseCoreArgs
    (args : List String) :
    Except String (ToCore.OutputDialect × Bool × String × Option String) := do
  let rec go
      (dialect : ToCore.OutputDialect)
      (useOfficialPrinter : Bool)
      (rest : List String) :
      Except String (ToCore.OutputDialect × Bool × String × Option String) := do
    match rest with
    | "--official" :: tail => go dialect true tail
    | "--dialect" :: d :: tail =>
      let dialect ←
        match parseOutputDialect? d with
        | some dialect => pure dialect
        | none => throw s!"unknown output dialect: {d}"
      go dialect useOfficialPrinter tail
    | [path] => pure (dialect, useOfficialPrinter, path, none)
    | [path, toFile] => pure (dialect, useOfficialPrinter, path, some toFile)
    | [] => throw "missing input path"
    | _ => throw "unexpected extra arguments"
  go .core false args

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

unsafe def genCoreFromFile
    (path : String)
    (printFn : String → IO Unit)
    (dialect : ToCore.OutputDialect := .core)
    (useOfficialPrinter : Bool := false) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let seqPreludeBody? ← readSeqPreludeBody?
  let vecPreludeBody? ← readVecPreludeBody?
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
        failWith e
      else
        -- Keep translating other shards so one unsupported module does not block output.
        IO.eprintln s!"warning: skipping shard {f}: {e}"
  let availableTextPreludes : ToCore.TextPreludeAvailability :=
    { seq := seqPreludeBody?.isSome, vec := vecPreludeBody?.isSome }
  match ToCore.declsToProgram allDecls allCallSiteTypes
      (availableTextPreludes := availableTextPreludes) with
  | .ok lowered =>
    let p := lowered.program
    let fnDecMap := lowered.fnDecMap
    let bodyText := ToString.toString (Std.Format.pretty (Strata.Core.formatProgram p) 100)
    let seqPreludeNeeded := lowered.neededPreludes.seq
    let vecPreludeNeeded := lowered.neededPreludes.vec
    let preludeText? := assemblePreludeText seqPreludeNeeded vecPreludeNeeded seqPreludeBody? vecPreludeBody?
    if useOfficialPrinter then
      if dialect != .core then
        failWith "--official only supports Core output"
      let output :=
        match preludeText? with
        | some prelude => prependPrelude .core prelude (bodyText ++ "\n")
        | none => s!"{programHeader .core}\n\n{bodyText}\n"
      printFn output
    else
      match ToCore.OutputPrep.prepareProgramForOutputDialect
          dialect p fnDecMap lowered.prunableDeclNames with
      | .ok p =>
        let body := ToCore.Pretty.programToString p dialect
        let output :=
          match preludeText? with
          | some prelude => prependPrelude dialect prelude body
          | none => body
        printFn output
      | .error e =>
        failWith e
  | .error e => failWith e

unsafe def genBooleFromFile
    (path : String)
    (printFn : String → IO Unit) : IO Unit := do
  let target := System.FilePath.mk path
  let bundleFiles ← collectJsonBundleFiles target
  let seqPreludeBody? ← readSeqPreludeBody?
  let vecPreludeBody? ← readVecPreludeBody?
  let mut allDecls : List Decl := []
  let mut allCallSiteTypes : CallSiteTypes := {}
  for f in bundleFiles do
    match ← Decls.fromFile? f.toString with
    | .ok (_ns, defs, thms, callTypes) =>
      allDecls := allDecls ++ defs ++ thms
      for (name, sig) in callTypes.toList do
        if !allCallSiteTypes.contains name then
          allCallSiteTypes := allCallSiteTypes.insert name sig
    | .error e =>
      if f == target then failWith e
      else IO.eprintln s!"warning: skipping shard {f}: {e}"
  let availableTextPreludes : ToCore.TextPreludeAvailability :=
    { seq := seqPreludeBody?.isSome, vec := vecPreludeBody?.isSome }
  match ToCore.declsToProgram allDecls allCallSiteTypes
      (availableTextPreludes := availableTextPreludes) with
  | .ok lowered =>
    let seqPreludeNeeded := lowered.neededPreludes.seq
    let vecPreludeNeeded := lowered.neededPreludes.vec
    let preludeText? := assemblePreludeText seqPreludeNeeded vecPreludeNeeded seqPreludeBody? vecPreludeBody?
    match ← Boole.CoreToBoole.renderBooleProgram lowered (preludeText? := preludeText?) with
    | .ok rendered => printFn rendered
    | .error e => failWith e
  | .error e => failWith e

unsafe def main : List String → IO Unit
  | [path] => genFromFile path IO.println
  | ["boole", path] => genBooleFromFile path IO.println
  | ["boole", path, toFile] => genBooleFromFile path (IO.FS.writeFile toFile)
  | ["boogie", path] => genCoreFromFile path IO.println
  | ["boogie", path, toFile] => genCoreFromFile path (IO.FS.writeFile toFile)
  | "core" :: args =>
    match parseCoreArgs args with
    | .error e =>
      failWith e
    | .ok (dialect, useOfficialPrinter, path, toFile?) =>
      match toFile? with
      | some toFile =>
        genCoreFromFile path (IO.FS.writeFile toFile) dialect (useOfficialPrinter := useOfficialPrinter)
      | none =>
        genCoreFromFile path IO.println dialect (useOfficialPrinter := useOfficialPrinter)
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
      ./verus-lean boole <input.json> [output.boole.st]\n\
      ./verus-lean boogie <input.json> [output.core.st]\n\
      ./verus-lean core [--official] [--dialect core|boole] <input.json> [output.st]"
