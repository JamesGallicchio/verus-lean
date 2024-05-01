import Lean
import VerusLean

open VerusLean

open Lean PrettyPrinter

opaque STOP_ON_ERROR : Bool := true

def format (formatter : Formatter) (stx : Syntax) : CoreM Format := do
  trace[PrettyPrinter.format.input] "{Std.format stx}"
  let options ← getOptions
  let table ← Parser.builtinTokenTable.get
  catchInternalId backtrackExceptionId
    (do
      let (_, st) ← (Formatter.concat formatter { table, options }).run { stxTrav := .fromSyntax stx }
      let mut f := st.stack[0]!
      if pp.oneline.get options then
        let mut s := f.pretty' options |>.trim
        let lineEnd := s.find (· == '\n')
        if lineEnd < s.endPos then
          s := s.extract 0 lineEnd ++ " [...]"
        -- TODO: preserve `Format.tag`s?
        f := s
      return .fill f)
    (fun ex => throwError "format: uncaught backtrack exception: {ex.toMessageData}")

unsafe def main (args : List String) : IO Unit := do
  let path := args[0]!
  let resPath := args[1]!
  IO.println s!"Reading file {path}"
  let json_str ← IO.FS.readFile path
  let fns ← do
    let arr ← IO.ofExcept <| (do (← Lean.Json.parse json_str).getArr?)
    arr.filterMapM fun j => do
      match Function.fromJson? j with
      | .ok j => return some j
      | .error e =>
        if STOP_ON_ERROR then
          throw (.userError e)
        else
          IO.println e
          return none
  IO.println s!"Converting functions to Lean syntax"
  let fns' ← Lean.withImportModules
    (imports := #[])
    (opts := default)
    (trustLevel := 0)
    <| fun env => EIO.toIO' <|
    Lean.Core.CoreM.run'
      (ctx := {
        fileName := "Example.lean"
        fileMap := default
      })
      (s := {
        env
      })
      (fns.filterMapM (fun f => do
        IO.println s!"{f.id.segments}: processing"
        try
          let syn ← Lean.liftCommandElabM (Function.toSyntax f)
          IO.println s!"{f.id.segments}: typechecking"
          Lean.liftCommandElabM <| Elab.Command.elabCommandTopLevel syn
          IO.println s!"{f.id.segments}: formatting"
          let fmt ← _root_.format (Formatter.categoryFormatter `command) syn
          IO.println s!"{f.id.segments}: done"
          return some fmt
        catch exc =>
          IO.println s!"{f.id.segments}: error: {← exc.toMessageData.toString}"
          return none)
      )
  match fns' with
  | .error exc =>
    IO.println (← exc.toMessageData.toString)
  | .ok fns' =>
  IO.println s!"Writing syntax to file {resPath}"
  let formatted : Lean.Format :=
    fns'.foldr (fun x acc => x ++ .line ++ .line ++ acc)
      ""
  IO.FS.writeFile resPath (formatted.pretty)
  IO.println s!"Finished!"
