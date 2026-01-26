/-

Basic facts and definitions.

Author: Cayden Codel
Carnegie Mellon University

-/

import Lean.Data.Json
import VerusLean.Basic.BitVec
import VerusLean.Basic.Monad
import VerusLean.Basic.UInt

namespace String

def cmp (s₁ s₂ : String) : Ordering :=
  if s₁ < s₂ then Ordering.lt
  else if s₁ = s₂ then Ordering.eq
  else Ordering.gt

@[simp]
theorem cmp_self (s : String) : s.cmp s = .eq := by simp [cmp]

@[simp]
theorem cmp_eq_iff {s₁ s₂ : String} : s₁.cmp s₂ = .eq ↔ s₁ = s₂ := by
  simp [cmp]
  split
  <;> rename_i h
  · simp
    rintro rfl
    simp at h
  · split
    <;> (simp; assumption)

end String

namespace Char

open Lean (Json ToJson FromJson)

/--
  Maps a `Char` to a JSON singleton.

  Because JSON has no special char field, we use a JSON singleton:

    { 'char': (<charVal> : Nat) }

  NOTE: Rust allows for some chars to use UTF-16 code points, while Lean
  requires UTF-8 encoding.
-/
def toJson (c : Char) : Json :=
  Json.obj (Std.TreeMap.Raw.empty.insert "char" (Json.num <| c.toNat))

/--
  Attemps to map a JSON back into a `Char`.

  Reverses the `toJson` function. (See above.)
-/
def fromJson? (j : Json) : Except String Char :=
  match j with
  | Json.obj o =>
    match o.get? "char" with
    | some (Json.num n) =>
      -- Assume that the underlying implementation of `JsonNumber.fromNat` sets the exponent to 0
      match n with
      | ⟨n, 0⟩ =>
        if n < 0 then
          .error s!"Numerical value under 'char' is negative, expected non-negative: {n}"
        else
          if hn : n.natAbs < UInt32.size then
            let fn : UInt32 := UInt32.ofNatLT n.natAbs hn
            if h_valid : fn.isValidChar then
              .ok <| Char.ofNatAux n.natAbs h_valid
            else
              .error s!"Numerical value under 'char' is not a valid Unicode scalar value: {n}"
          else
            .error s!"Numerical value under 'char' is too large, expected less than {UInt32.size}: {n}"
      | _ => .error s!"Numerical value under 'char' is not an integer, got {n}"
    | some d            => .error s!"Data under 'char' field is not a number, got {d}"
    | _                 => .error s!"Missing data under 'char' field"
  | _ => .error s!"Expected a singleton object with a 'char' field. Got: {j}"

instance instToJson : ToJson Char where
  toJson := toJson

instance instFromJson : FromJson Char where
  fromJson? := fromJson?

@[simp]
theorem fromJson?_toJson (c : Char) : fromJson? (toJson c) = Except.ok c := by
    simp [toJson, fromJson?]
    stop
    split
    <;> rename_i h_find
    · simp [Lean.RBNode.find] at h_find
      done
    have h : Char.ofNatAux c.toNat (Char.isValidChar c) = c := Char.ofNatAux_eq_of_valid_char c
    rw [h]
    rfl

end Char
