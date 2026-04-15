/-
  Boole.Signatures — translator-known signatures for prelude/helper symbols.

  These signatures are used for expected-type propagation while lowering VLIR.
  They describe the helper surface the translator knows about; textual Boole
  prelude files still own the declarations/bodies for prelude-provided names.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Coercions

namespace VerusLean.Boole.Signatures

open VerusLean
open VerusLean.Boole.Coercions

def knownFnSignature? (fname : String) : Option (List Typ × Typ) :=
  let t := Typ.TypParam "T"
  let a := Typ.TypParam "A"
  let b := Typ.TypParam "B"
  let seqT := Typ.Struct (.str (.str .anonymous "vstd") "Seq") [t]
  let setT := Typ.Struct (.str (.str .anonymous "vstd") "Set") [t]
  let vecT := Typ.Struct (.str (.str .anonymous "vstd") "Vec") [t]
  let mapAB := Typ.Struct (.str (.str .anonymous "vstd") "Map") [a, b]
  let registry : List (String × (List Typ × Typ)) :=
    [ ("Seq_index",        ([seqT, .Int], t))
    , ("Seq_update",       ([seqT, .Int, t], seqT))
    , ("Seq_push",         ([seqT, t], seqT))
    , ("Seq_take",         ([seqT, .Int], seqT))
    , ("Seq_skip",         ([seqT, .Int], seqT))
    , ("Seq_add",          ([seqT, seqT], seqT))
    , ("Seq_first",        ([seqT], t))
    , ("Seq_last",         ([seqT], t))
    , ("Seq_subrange",     ([seqT, .Int, .Int], seqT))
    , ("Seq_lib_contains", ([seqT, t], .Bool))
    , ("Seq_lib_drop_last",([seqT], seqT))
    , ("Seq_lib_remove",   ([seqT, .Int], seqT))
    , ("Seq_len",          ([seqT], .Nat))
    , ("Seq_lib_insert",   ([seqT, .Int, t], seqT))
    , ("Seq_new",          ([.Nat, .SpecFn [.Int] t], seqT))
    , ("Seq_lib_map",      ([Typ.Struct (.str (.str .anonymous "vstd") "Seq") [a], .SpecFn [.Int, a] b],
                            Typ.Struct (.str (.str .anonymous "vstd") "Seq") [b]))
    , ("Seq_lib_map_values",([Typ.Struct (.str (.str .anonymous "vstd") "Seq") [a], .SpecFn [a] b],
                             Typ.Struct (.str (.str .anonymous "vstd") "Seq") [b]))
    , ("Seq_lib_filter",   ([seqT, .SpecFn [t] .Bool], seqT))
    , ("Seq_lib_sort_by",  ([seqT, .SpecFn [t, t] .Bool], seqT))
    , ("Seq_lib_to_set",   ([seqT], setT))
    , ("Set_finite",       ([setT], .Bool))
    , ("nat_to_int",       ([.Nat], .Int))
    , ("int_to_nat",       ([.Int], .Nat))
    , ("Vec_len",          ([vecT], .UInt usizeBitWidth))
    , ("Vec_index",        ([vecT, .UInt usizeBitWidth], t))
    , ("Vec_view",         ([vecT], seqT))
    , ("Set_contains",     ([setT, a], .Bool))
    , ("Map_index",        ([mapAB, a], b))
    ]
  let castSig := supportedBvWidths.findSome? (fun w =>
    if fname == s!"bv{w}_to_int_u" then some ([.UInt w], .Int)
    else if fname == s!"bv{w}_to_int_s" then some ([.SInt w], .Int)
    else if fname == s!"bv{w}_to_nat_u" then some ([.UInt w], .Nat)
    else if fname == s!"bv{w}_to_nat_s" then some ([.SInt w], .Nat)
    else if fname == s!"int_to_bv{w}_u" then some ([.Int], .UInt w)
    else if fname == s!"int_to_bv{w}_s" then some ([.Int], .SInt w)
    else none)
  -- bv-widening/narrowing casts: `bv{from}_to_bv{to}_{u,s}` must be
  -- registered alongside their emitters in `Coercions.bvWidenCastName`.
  let bvWidenSig := supportedBvWidths.findSome? (fun fromW =>
    supportedBvWidths.findSome? (fun toW =>
      if fname == s!"bv{fromW}_to_bv{toW}_u" then some ([.UInt fromW], .UInt toW)
      else if fname == s!"bv{fromW}_to_bv{toW}_s" then some ([.SInt fromW], .SInt toW)
      else none))
  (registry.find? (fun (n, _) => n == fname) |>.map Prod.snd) <|> castSig <|> bvWidenSig

def lookupKnownFnRetType (fname : String) : Option Typ :=
  (knownFnSignature? fname).map Prod.snd

def lookupKnownFnParamType (fname : String) (idx : Nat) : Option Typ := do
  let (params, _) ← knownFnSignature? fname
  params.drop idx |>.head?

end VerusLean.Boole.Signatures
