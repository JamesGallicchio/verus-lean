import Lean.Data.Json
import VerusLean

open VerusLean


unsafe def main (args : List String) : IO Unit := do
  let path := args[0]!
  let resPath := args[1]!
  IO.println s!"Reading file {path}"
  let json_str ← IO.FS.readFile path
  let fns ← IO.ofExcept <| do
    let json ← Lean.Json.parse json_str
    let arr ← json.getArr?
    arr.mapM Function.fromJson?
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
      (Lean.liftCommandElabM <| (fns.mapM (fun f => Function.toSyntax f)))
  match fns' with
  | .error exc =>
    IO.println (← exc.toMessageData.toString)
  | .ok fns' =>
  IO.println s!"Writing syntax to file {resPath}"
  let formatted : Lean.Format :=
    fns'.foldr (fun x acc => x.prettyPrint ++ .line ++ .line ++ acc)
      ""
  IO.FS.writeFile resPath (formatted.pretty (width := 30))
  IO.println s!"Finished!"
