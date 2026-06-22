/-
  Boole.Coercions — numeric type classification and cast-name metadata.

  Policy invariant: source variables keep their source type.  When mixed
  integer/bitvector expressions require a common domain, lowering inserts
  explicit cast-helper applications instead of retargeting variables.

  This module stays pure (no `BuildM`, no IO) so metadata modules such as
  `Signatures` can depend on it without transitively pulling `StrataDDM`'s IO layer.
  The `BuildM`-valued cast-insertion helpers live in `Cast.lean`.
-/
import VerusLean.VLIR.Defs

namespace VerusLean.Boole.Coercions

open VerusLean

def usizeBitWidth : Nat := 64

-- Bitvector widths the Boole backend models natively.  Covers every
-- fixed-width Rust integer type (`u8`..`u128`/`i8`..`i128`); `usize`/`isize`
-- map to `usizeBitWidth`.  `u128`/`i128` are full `bv128` with native bv ops.
def supportedBvWidths : List Nat := [1, 8, 16, 32, 64, 128]

def isSupportedBvWidth (w : Nat) : Bool :=
  supportedBvWidths.contains w

def bitWidthOfTyp : Typ → Option Nat
  | .UInt w | .SInt w => if isSupportedBvWidth w then some w else none
  | .USize | .ISize => some usizeBitWidth
  | .Decorated _ ty => bitWidthOfTyp ty
  | _ => none

def bitInfoOfTyp : Typ → Option (Nat × Bool)
  | .UInt w => if isSupportedBvWidth w then some (w, false) else none
  | .SInt w => if isSupportedBvWidth w then some (w, true) else none
  | .USize => some (usizeBitWidth, false)
  | .ISize => some (usizeBitWidth, true)
  | .Decorated _ ty => bitInfoOfTyp ty
  | _ => none

/-- Width and signedness of any fixed-width integer type, unconditionally — it
    does not gate on `isSupportedBvWidth`.  Contrast `bitInfoOfTyp`, which
    answers "what bitvector width, if any" and stays `none` for a width outside
    `supportedBvWidths`. -/
def fixedWidthInfoOfTyp : Typ → Option (Nat × Bool)
  | .UInt w => some (w, false)
  | .SInt w => some (w, true)
  | .USize => some (usizeBitWidth, false)
  | .ISize => some (usizeBitWidth, true)
  | .Decorated _ ty => fixedWidthInfoOfTyp ty
  | _ => none

/-- Every value of a `(srcW, srcSigned)` fixed-width type is representable in
    a `(tgtW, tgtSigned)` fixed-width type — i.e. the cast between them never
    wraps, so its truncation may be elided. -/
def fitsFixedWidth (src tgt : Nat × Bool) : Bool :=
  match src, tgt with
  | (sw, false), (tw, false) => decide (sw ≤ tw)
  | (sw, false), (tw, true)  => decide (sw < tw)
  | (sw, true),  (tw, true)  => decide (sw ≤ tw)
  | (_,  true),  (_,  false) => false

def isIntTyp : Typ → Bool
  | .Int => true
  | .Decorated _ ty => isIntTyp ty
  | _ => false

def isUnitLikeTyp : Typ → Bool
  | .Unit | .Empty => true
  | .Decorated _ ty => isUnitLikeTyp ty
  | _ => false

def bitTypOfInfo (w : Nat) (signed : Bool) : Typ :=
  if signed then Typ.SInt w else Typ.UInt w

/-- Numeric type classification for coercion decisions. -/
inductive NumKind where
  | int
  | nat
  | bv (w : Nat) (signed : Bool)
  deriving DecidableEq, Repr

/-- The modeled numeric *domain* of a type — the single source of truth for
    coercion decisions.  Every fixed-width integer type (`supportedBvWidths`,
    which includes `u128`/`i128`) is a `.bv`; `int`/`nat` are the mathematical
    domains.  Exec-mode wrapping arithmetic lowers in the bv domain at the type's
    native width.  Spec-mode `+ - * /` is recorded with an `int`/`nat` result
    type in VLIR and stays mathematical (the `parentIntNatClip` rule in
    `Parser`), so a u128-typed spec value reaches its `as u128` cast as a
    faithful unbounded `int`, then casts exactly to `bv128`. -/
def numKindOfTyp? : Typ → Option NumKind
  | .Int => some .int
  | .Nat => some .nat
  | .UInt w => if isSupportedBvWidth w then some (.bv w false) else some .int
  | .SInt w => if isSupportedBvWidth w then some (.bv w true) else some .int
  | .USize => some (.bv usizeBitWidth false)
  | .ISize => some (.bv usizeBitWidth true)
  | .Decorated _ ty => numKindOfTyp? ty
  | _ => none

def bvToIntCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_int_s" else s!"bv{w}_to_int_u"

def bvToNatCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"bv{w}_to_nat_s" else s!"bv{w}_to_nat_u"

def intToBvCastName (w : Nat) (signed : Bool) : String :=
  if signed then s!"int_to_bv{w}_s" else s!"int_to_bv{w}_u"

def bvWidenCastName (fromW toW : Nat) (signed : Bool) : String :=
  if signed then s!"bv{fromW}_to_bv{toW}_s" else s!"bv{fromW}_to_bv{toW}_u"

def canPromoteBvWidths (fromW toW : Nat) : Bool :=
  isSupportedBvWidth fromW && isSupportedBvWidth toW && fromW <= toW

def choosePromotionWidth? (w1 w2 : Nat) : Option Nat :=
  let w := max w1 w2
  if canPromoteBvWidths w1 w && canPromoteBvWidths w2 w then some w else none

def chooseBitPromotionInfo?
    (lhsInfo rhsInfo : Nat × Bool) : Option (Nat × Bool) :=
  let (w1, s1) := lhsInfo
  let (w2, s2) := rhsInfo
  if s1 == s2 then
    (choosePromotionWidth? w1 w2).map (fun w => (w, s1))
  else
    none

end VerusLean.Boole.Coercions
