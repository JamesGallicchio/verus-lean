import Batteries

open Lean Elab Command

namespace Lean.FromJson

instance : FromJson (Fin n) where
  fromJson? j := do
    let i : Nat ← fromJson? j
    if h : _ then
      return ⟨i,h⟩
    else
      throw s!"expected number < {n}, got {i}"

#eval show CommandElabM Unit from do
  let tys := #[``UInt8, ``UInt16, ``UInt32, ``UInt64]

  for t in tys do
    elabCommand <| ← `(command|
      instance : $(mkIdent ``Lean.FromJson) $(mkIdent t) where
        fromJson? j := do
          let i: Nat ← fromJson? j
          if h : _ then
            return ⟨i,h⟩
          else
            throw s!"{$(Syntax.mkStrLit t.toString)}: {i} out of range"
    )

end Lean.FromJson

namespace Lean.ToJson

#eval show CommandElabM Unit from do
  let tys := #[``UInt8, ``UInt16, ``UInt32, ``UInt64]

  for t in tys do
    elabCommand <| ← `(command|
      instance : Lean.ToJson $(mkIdent t) where
        toJson i := toJson i.val.val
    )

end Lean.ToJson
