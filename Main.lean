import Lean
import VerusLean

open VerusLean

opaque STOP_ON_ERROR : Bool := true

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
        IO.println s!"processing {f.id.segments}"
        Lean.liftCommandElabM <| do
        try
          let syn ← Function.toSyntax f
          return some syn
        catch _ =>
          return none
      ))
  match fns' with
  | .error exc =>
    IO.println (← exc.toMessageData.toString)
  | .ok fns' =>
  IO.println s!"Writing syntax to file {resPath}"
  let formatted : Lean.Format :=
    fns'.foldr (fun x acc => x.prettyPrint ++ .line ++ .line ++ acc)
      ""
  IO.FS.writeFile resPath (formatted.pretty)
  IO.println s!"Finished!"
