/-
  Boole.Ops — Per-operator BExpr builders.

  Maps VLIR `BinaryOp` / `UnaryOp` and the bv operator-name strings the
  translator passes around (e.g. "Add", "ULt") to the corresponding
  Builder constructors. Pure, no `BuildM` — each function returns
  `Option BExpr` so callers can detect unsupported operators and either
  fall back or raise a translator error.

  Bv-specific arithmetic (`applyBvBinOp`), bitwise (`applyBvBitOp`), and
  comparison (`applyBvCmpOp`) are split for symmetry with the
  width-keyed bv builder names; the generic `applyBinaryOp` /
  `applyUnaryOp` cover the int/bool cases that don't carry a width
  parameter.
-/
import VerusLean.VLIR.Defs
import VerusLean.VLIR.Boole.Bld

namespace VerusLean.Boole.Ops

open VerusLean
open VerusLean.Boole.Bld

/-- Apply a binary bitvector operation. -/
def applyBvBinOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "Add" => some (bvAdd w a b)
  | "Sub" => some (bvSub w a b)
  | "Mul" => some (bvMul w a b)
  | "UDiv" => some (bvUDiv w a b)
  | "UMod" => some (bvUMod w a b)
  | "SDiv" => some (bvSDiv w a b)
  | "SMod" => some (bvSMod w a b)
  | _ => none

/-- Apply a bitvector bitwise operation. -/
def applyBvBitOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "And" => some (bvAnd w a b)
  | "Or" => some (bvOr w a b)
  | "Xor" => some (bvXor w a b)
  | "Shl" => some (bvShl w a b)
  | "UShr" => some (bvUShr w a b)
  | _ => none

/-- Apply a bitvector comparison operation. -/
def applyBvCmpOp (w : Nat) (opName : String) (a b : BExpr) : Option BExpr :=
  match opName with
  | "ULt" => some (bvUlt w a b)
  | "ULe" => some (bvUle w a b)
  | "UGt" => some (bvUgt w a b)
  | "UGe" => some (bvUge w a b)
  | "SLt" => some (bvSlt w a b)
  | "SLe" => some (bvSle w a b)
  | "SGt" => some (bvSgt w a b)
  | "SGe" => some (bvSge w a b)
  | _ => none

def applyBinaryOp (op : BinaryOp) (a b : BExpr) : Option BExpr :=
  match op with
  | .And => some (boolAnd a b)
  | .Or => some (boolOr a b)
  | .Implies => some (boolImplies a b)
  | .Arith .Add _ => some (intAdd a b)
  | .Arith .Sub _ => some (intSub a b)
  | .Arith .Mul _ => some (intMul a b)
  | .Arith .EuclideanDiv _ => some (intDiv a b)
  | .Arith .EuclideanMod _ => some (intMod a b)
  | .Inequality .Le => some (intLe a b)
  | .Inequality .Lt => some (intLt a b)
  | .Inequality .Ge => some (intGe a b)
  | .Inequality .Gt => some (intGt a b)
  | _ => none

def applyUnaryOp (op : UnaryOp) (a : BExpr) : Option BExpr :=
  match op with
  | .Not => some (boolNot a)
  | _ => none

end VerusLean.Boole.Ops
