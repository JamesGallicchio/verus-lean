/-
  Boole.Support — pure metadata for translator-emitted support declarations.

  Keep names and signatures for `SupportDecl` in one place. Emission of the
  corresponding BooleDDM commands lives in `SupportEmit.lean`; this module
  deliberately stays pure so signature/type-inference code can import it
  without pulling in the rendering/IO layer.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Context
import VerusLean.VLIR.Boole.Coercions

namespace VerusLean.Boole.Support

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.Context (SupportDecl)

def supportDeclName : SupportDecl → String
  | .nat => "nat"
  | .natToInt => "nat_to_int"
  | .intToNat => "int_to_nat"
  | .bvToInt w signed => bvToIntCastName w signed
  | .bvToNat w signed => bvToNatCastName w signed
  | .intToBv w signed => intToBvCastName w signed
  | .bvWiden fromW toW signed => bvWidenCastName fromW toW signed
  | .tuple => "Tuple"
  | .seqZipWith => "Seq_lib_zip_with"

def supportDeclUsesNat : SupportDecl → Bool
  | .nat | .natToInt | .intToNat | .bvToNat .. => true
  | _ => false

def supportDeclSignature? : SupportDecl → Option (List Typ × Typ)
  | .nat | .tuple | .seqZipWith => none
  | .natToInt => some ([.Nat], .Int)
  | .intToNat => some ([.Int], .Nat)
  | .bvToInt w signed =>
    some ([bitTypOfInfo w signed], .Int)
  | .bvToNat w signed =>
    some ([bitTypOfInfo w signed], .Nat)
  | .intToBv w signed =>
    some ([.Int], bitTypOfInfo w signed)
  | .bvWiden fromW toW signed =>
    some ([bitTypOfInfo fromW signed], bitTypOfInfo toW signed)

def numericSupportDecls : List SupportDecl :=
  [.natToInt, .intToNat] ++
  supportedBvWidths.flatMap (fun w =>
    [ .bvToInt w false, .bvToInt w true
    , .bvToNat w false, .bvToNat w true
    , .intToBv w false, .intToBv w true
    ]) ++
  supportedBvWidths.flatMap (fun fromW =>
    supportedBvWidths.flatMap (fun toW =>
      if fromW < toW then
        [.bvWiden fromW toW false, .bvWiden fromW toW true]
      else
        []))

def allSupportDecls : List SupportDecl :=
  -- Order matters for emission: `.tuple` declares the `Tuple` datatype
  -- that `.seqZipWith` refers to in its return type, so `.seqZipWith`
  -- must come after it.
  [.tuple, .nat] ++ numericSupportDecls ++ [.seqZipWith]

def supportDeclForName? (fname : String) : Option SupportDecl :=
  allSupportDecls.find? (fun need => supportDeclName need == fname)

end VerusLean.Boole.Support
