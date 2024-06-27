import VerusLean.Lean
import Qq

namespace VerusLean.Macro

open Lean Meta Elab Command
open Qq

def readAndGen (files : Term) : CommandElabM (TSyntaxArray `command) := do
  let file ← liftTermElabM <| do
    let expr ← Term.elabTerm files (some q(System.FilePath))
    unsafe evalExpr (System.FilePath) (q(System.FilePath)) expr

  let json ← IO.ofExcept <| Lean.Json.parse <| ← IO.FS.readFile file

  let funcs : Array Decl ← IO.ofExcept <| Lean.fromJson? json

  logInfo m!"Processing {funcs.size} functions"
  let res ← funcs.mapM (fun f => do
    try
      return ← Decl.toSyntax f
    catch e =>
      logWarning e.toMessageData
      return #[])
  return res.flatten


syntax (name := generate_verus_funcs)
  "#generate_verus_funcs " term (" {{" (ppLine command)* ppDedent(ppLine "}}") )? : command

deriving instance TypeName for String

@[command_elab generate_verus_funcs]
def genCapnProtoHandler : CommandElab := fun stx => do
  match stx with
  | `(command| #generate_verus_funcs $files:term ) =>
    let res ← readAndGen files
    let fmt ← format files res
    pushInfoLeaf (.ofCustomInfo {
        stx := ← getRef,
        value := Dynamic.mk fmt.pretty })
    for c in res do elabCommand c
  | `(command| #generate_verus_funcs $files:term {{ $c:command* }} ) =>
    let res ← readAndGen files
    if res != c then
      let fmt ← format files res
      pushInfoLeaf (.ofCustomInfo {
        stx := ← getRef,
        value := Dynamic.mk fmt.pretty })
    for c in c do elabCommand c
  | _ =>
    throwUnsupportedSyntax
where format (files : Term) (cmds : TSyntaxArray `command) : CommandElabM Format := do
  let syn ← `(command|
    #generate_verus_funcs $files {{
      $cmds:command*
    }}
  )
  let parenthesized ← liftCoreM <| Lean.PrettyPrinter.parenthesizeCommand syn
  return ← liftCoreM <| Lean.PrettyPrinter.formatCommand parenthesized

open CodeAction Server RequestM in
@[command_code_action generate_verus_funcs]
def guardMsgsCodeAction : CommandCodeAction := fun _ _ _ node => do
  let .node _ ts := node | return #[]
  let res := ts.findSome? fun
    | .node (.ofCustomInfo { stx, value }) _ => return (stx, (← value.get? String))
    | _ => none
  let some (stx, newText) := res | return #[]
  let eager := {
    title := "Update #generate_verus_funcs with correct output"
    kind? := "quickfix"
    isPreferred? := true
  }
  let doc ← readDoc
  pure #[{
    eager
    lazy? := some do
      let some start := stx.getPos? true | return eager
      let some tail := stx.getTailPos? true | return eager
      pure {
        eager with
        edit? := some <| .ofTextEdit doc.versionedIdentifier {
          range := doc.meta.text.utf8RangeToLspRange ⟨start, tail⟩
          newText
        }
      }
  }]
