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
import VerusLean.VLIR.Boole.Names

namespace VerusLean.Boole.Support

open VerusLean
open VerusLean.Boole.Coercions
open VerusLean.Boole.Context (SupportDecl)
open VerusLean.Boole.Names (tupleTypeName)

def supportDeclName : SupportDecl → String
  | .nat => "nat"
  | .natToInt => "nat_to_int"
  | .intToNat => "int_to_nat"
  | .bvToInt w signed => bvToIntCastName w signed
  | .bvToNat w signed => bvToNatCastName w signed
  | .intToBv w signed => intToBvCastName w signed
  | .bvWiden fromW toW signed => bvWidenCastName fromW toW signed
  | .tuple => tupleTypeName
  | .seqZipWith => "Seq_lib_zip_with"
  | .arrayFill => "Array_array_fill_for_copy_types"
  | .set => "Set"
  | .seqNew => "Seq_new"
  | .seqLibMap => "Seq_lib_map"
  | .seqLibMapValues => "Seq_lib_map_values"
  | .seqLibFilter => "Seq_lib_filter"
  | .seqLibSortBy => "Seq_lib_sort_by"
  | .seqLibToSet => "Seq_lib_to_set"
  | .setFinite => "Set_finite"

def supportDeclUsesNat : SupportDecl → Bool
  -- `Seq_new`'s first parameter is `len : nat`.
  | .nat | .natToInt | .intToNat | .bvToNat .. | .seqNew => true
  | _ => false

def supportDeclSignature? : SupportDecl → Option (List Typ × Typ)
  -- The Seq higher-order / Set builtins use custom builders in `SupportEmit`
  -- (arrow-typed params / multiple type params that the `[input] → output`
  -- shape here can't express), so they return `none`.
  | .nat | .tuple | .seqZipWith | .arrayFill
  | .set | .seqNew | .seqLibMap | .seqLibMapValues | .seqLibFilter
  | .seqLibSortBy | .seqLibToSet | .setFinite => none
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
  -- Order matters for emission: a decl's type references must already be
  -- declared.  `.tuple` precedes `.seqZipWith` (return type `Sequence
  -- (Tuple ..)`); `.set` precedes `.seqLibToSet` / `.setFinite` (which
  -- mention `Set ..` in their signatures).
  [.tuple, .nat] ++ numericSupportDecls ++
    [.seqZipWith, .arrayFill,
     .set, .seqNew, .seqLibMap, .seqLibMapValues, .seqLibFilter,
     .seqLibSortBy, .seqLibToSet, .setFinite]

def supportDeclForName? (fname : String) : Option SupportDecl :=
  allSupportDecls.find? (fun need => supportDeclName need == fname)

end VerusLean.Boole.Support
