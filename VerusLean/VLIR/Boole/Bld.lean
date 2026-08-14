/-
  Boole.Bld — shared alias namespace for Builder symbols.

  We intentionally do NOT `open VerusLean.Boole.Builder` in translator modules
  because some of its names (`fvar`, `bvar`, `app`, `eq`, `old`, …) conflict
  with Lean builtins or BooleDDM constructors inside `mutual` blocks. Both
  `Cast.lean` and `Translate.lean` used to duplicate the same `namespace Bld`
  export block; this module hoists it so they share one source of truth.
-/
import VerusLean.VLIR.Boole.Builder

namespace VerusLean.Boole.Bld

export VerusLean.Boole.Builder (
  BExpr BType BStmt BCmd BBlock
  boolTy intTy strTy bvTy mapTy seqTy arrowTy tvarTy fvarTy unknownTy
  fvar bvar boolConst intConst bitvecConstNat bitvecConst
  castToInt castToSInt castToBv
  ite iteTyped eq neq eqTyped neqTyped app appN
  boolNot boolAnd boolOr boolImplies boolEquiv
  intAdd intSub intMul intDiv intMod intNeg
  intLe intLt intGe intGt
  bvAdd bvSub bvMul bvUDiv bvUMod bvSDiv bvSMod bvNeg
  bvAnd bvOr bvXor bvNot bvShl bvUShr
  bvUle bvUlt bvUge bvUgt bvSle bvSlt bvSge bvSgt
  mapGet mapSet seqLength seqSelect seqUpdate seqEmpty old oldTyped
  forallExpr existsExpr forallExprT existsExprT lambdaExpr
  varStmt initStmt setStmt havocStmt chooseAssignStmt
  assertStmt assumeStmt coverStmt callStmt blockStmt setStmtTyped
  iteStmt whileStmt forToStmt exitStmt returnStmt
  mkMeasure
)

end VerusLean.Boole.Bld
