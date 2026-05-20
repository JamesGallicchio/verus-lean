/-
  Boole.Signatures — translator-known signatures for prelude/helper symbols.

  These signatures are used for expected-type propagation while lowering VLIR.
  They describe the helper surface the translator knows about; textual Boole
  prelude files still own the declarations/bodies for prelude-provided names.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Prelude
import VerusLean.VLIR.Boole.Support

namespace VerusLean.Boole.Signatures

open VerusLean
open VerusLean.Boole.Prelude
open VerusLean.Boole.Support

def knownFnSignature? (fname : String) : Option (List Typ × Typ) :=
  let a := Typ.TypParam "A"
  let b := Typ.TypParam "B"
  let mapAB := Typ.Struct (.str (.str .anonymous "vstd") "Map") [a, b]
  let registry : List (String × (List Typ × Typ)) :=
    knownPreludeSignatures ++
    [ ("Set_contains",     ([setTyp a, a], .Bool))
    , ("Map_index",        ([mapAB, a], b))
    , ("Arithmetic_Power2_pow2", ([.Nat], .Nat))
    ]
  (registry.find? (fun (n, _) => n == fname) |>.map Prod.snd) <|>
    (supportDeclForName? fname >>= supportDeclSignature?)

def lookupKnownFnRetType (fname : String) : Option Typ :=
  (knownFnSignature? fname).map Prod.snd

def lookupKnownFnParamType (fname : String) (idx : Nat) : Option Typ := do
  let (params, _) ← knownFnSignature? fname
  params.drop idx |>.head?

end VerusLean.Boole.Signatures
