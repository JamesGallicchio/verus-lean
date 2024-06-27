import VerusLean.Upstream

/-! # VLIR
A much reduced AST for Verus terms. -/

namespace VerusLean
open Lean (Json ToJson FromJson)

def Ident := String
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

def Idents := Array Ident
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

structure Binder (A : Type) where
  name: Ident
  a: A
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

abbrev Binders (A) := Array (Binder A)

/-- A fully-qualified name, such as a module name, function name, or datatype name -/
structure Path where
  /-- None for local crate -/
  krate: Option Ident
  segments: Idents
deriving ToJson, FromJson, Repr, DecidableEq, Hashable, Inhabited

/-- Describes integer types -/
inductive IntRange where
  /-- The set of all mathematical integers Z (..., -2, -1, 0, 1, 2, ...) -/
  | Int
  /-- The set of all natural numbers N (0, 1, 2, ...) -/
  | Nat
  /-- n-bit unsigned numbers (natural numbers up to 2^n - 1) for the specified n: u32 -/
  | U : UInt32 → IntRange
  /-- n-bit signed numbers (integers -2^(n-1), ..., 2^(n-1) - 1) for the specified n: u32 -/
  | I : UInt32 → IntRange
  /-- Rust's USize type -/
  | USize
  /-- Rust's isize type -/
  | ISize
deriving ToJson, FromJson, Repr, DecidableEq, Inhabited

/-- Rust type, but without Box, Rc, Arc, etc. -/
inductive Typ
  /-- Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed) -/
  | Bool
  | Int : IntRange → Typ
  /-- UTF-8 character type -/
  | Char
  /--
    `FnSpec` type (TODO rename from 'Lambda' to just 'FnSpec')
    (t1, ..., tn) -> t0. -/
  | Lambda : Array Typ → Typ → Typ
  /-- Datatype (concrete or abstract) applied to type arguments -/
  | Datatype : Path → Array Typ → Typ
  | Array : Typ → Typ → Typ
  | Slice : Typ → Typ
  /-- Type parameter (inherently SMT-boxed, and cannot be unboxed) -/
  | TypParam : Ident → Typ
  /-- Const integer type argument (e.g. for array sizes) -/
  | ConstInt : Int → Typ
deriving ToJson, FromJson, Repr, Inhabited

-- /// Primitive constant values
inductive Constant
    -- /// true or false
  | Bool : Bool → Constant
    -- /// integer of arbitrary size
  | Int : String → Constant
    -- /// Hold generated string slices in here
  | StrSlice : String → Constant
    -- Hold unicode values here
    -- The standard library doesn't use char constants and i'm not sure how they are encoded by serde
  -- | Char : Char → Constant
deriving ToJson, FromJson, Repr, DecidableEq

/-- Primitive unary operations
 (not arbitrary user-defined functions -- these are represented by Expr::Call) -/
inductive UnaryOp where
  /-- Boolean not -/
  | Not
  /-- bitwise not -/
  | BitNot
  /-- Force integer value into range given by IntRange (e.g. by using mod) -/
  | Clip (range: IntRange) (truncate: Bool)
    /-
    -- /// Used only for handling builtin::strslice_len
    StrLen,
    -- /// Used only for handling builtin::strslice_is_ascii
    StrIsAscii,
    -- /// Used only for handling casts from chars to ints
    CharToInt,
    -- /// May need coercion after casting a type argument
    CastToInteger,
    -/
  | Id
deriving ToJson, FromJson, Repr

-- /// Arithmetic operation that might fail (overflow or divide by zero)
inductive ArithOp
    -- /// IntRange::Int +
  | Add
    -- /// IntRange::Int -
  | Sub
    -- /// IntRange::Int *
  | Mul
    -- /// IntRange::Int / defined as Euclidean (round towards -infinity, not round-towards zero)
  | EuclideanDiv
    -- /// IntRange::Int % defined as Euclidean (returns non-negative result even for negative divisor)
  | EuclideanMod
deriving ToJson, FromJson, Repr, DecidableEq

-- /// Bitwise operation
inductive BitwiseOp
  | BitXor
  | BitAnd
  | BitOr
  | Shr
  | Shl
deriving ToJson, FromJson, Repr, DecidableEq


inductive InequalityOp
  | Le
  | Ge
  | Lt
  | Gt
deriving ToJson, FromJson, Repr, DecidableEq

inductive ChainedOp
  | Inequality : InequalityOp → ChainedOp
  | MultiEq
deriving ToJson, FromJson, Repr, DecidableEq

-- /// Primitive binary operations
-- /// (not arbitrary user-defined functions -- these are represented by Expr::Call)
-- /// Note that all integer operations are on mathematic integers (IntRange::Int),
-- /// not on finite-width integer types or nat.
-- /// Finite-width and nat operations are represented with a combination of IntRange::Int operations
-- /// and UnaryOp::Clip.
inductive BinaryOp
    -- /// Boolean and (short-circuiting: right side is evaluated only if left side is true)
  | And
    -- /// Boolean or (short-circuiting: right side is evaluated only if left side is false)
  | Or
    -- /// Boolean xor (no short-circuiting)
  | Xor
    -- /// Boolean implies (short-circuiting: right side is evaluated only if left side is true)
  | Implies
    -- /// SMT equality for any type -- two expressions are exactly the same value
    -- /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
  | Eq
    -- /// not Eq
  | Ne
    -- /// arithmetic inequality
  | Inequality : InequalityOp → BinaryOp
    -- /// IntRange operations that may require overflow or divide-by-zero checks
  | Arith : ArithOp → BinaryOp
    -- /// Bit Vector Operators
    -- /// mode=Exec means we need overflow-checking
  | Bitwise : BitwiseOp → BinaryOp
    -- /// Used only for handling builtin::strslice_get_char
  | StrGetChar
deriving ToJson, FromJson, Repr, DecidableEq

inductive MultiOp
  | Chained : Array ChainedOp → MultiOp
deriving ToJson, FromJson, Repr, DecidableEq

inductive Quant
  | Forall
  | Exists
deriving ToJson, FromJson, Repr, DecidableEq

inductive Expr : Type
    -- /// Constant
  | Const : Constant → Expr
    -- /// Local variable as a right-hand side
  | Var : Ident → Expr
    -- /// Call to a function passing some expression arguments
  | App : Expr → Array Expr → Expr
    -- /// Construct datatype value of type Path and variant Ident,
    -- /// with field initializers Binders<Expr> and an optional ".." update expression.
    -- /// For tuple-style variants, the fields are named "_0", "_1", etc.
    -- /// Fields can appear **in any order** even for tuple variants.
  | Ctor : Path → Ident → Array (Binder Expr)  → Option Expr → Expr
    -- /// Primitive unary operation
  | Unary : UnaryOp → Expr → Expr
    -- /// Primitive binary operation
  | Binary : BinaryOp → Expr → Expr → Expr
    -- /// Primitive multi-operand operation
  | Multi : MultiOp → Array Expr → Expr
    -- /// If-else
  | If: Expr → Expr → Expr → Expr
    -- Let binding
  | Let : Binder Expr → Expr → Expr
    -- /// Quantifier (forall/exists), binding the variables in Binders, with body Expr
  | Quant : Quant → Binders Typ → Expr → Expr
    -- /// Array literal (can also be used for sequence literals in the future)
  | ArrayLiteral : Array Expr → Expr
    -- /// Executable function (declared with 'fn' and referred to by name)
  | StaticFun : Path → Expr
    -- /// Choose specification values satisfying a condition, compute body
  | Choose
        (params: Binders Typ)
        (cond: Expr)
        (body: Expr)
deriving ToJson, FromJson, Repr, Inhabited

-- /// Function, including signature and body
structure Defn where
    -- /// Name of function
    name: Path
    -- /// Type parameters to generic functions
    -- /// (for trait methods, the trait parameters come first, then the method parameters)
    typ_params: Idents
    -- /// Function parameters
    params: Binders Typ
    -- /// Return value (unit return type is treated specially; see FunctionX::has_return in ast_util)
    ret: Binder Typ
    -- /// Body
    body: Expr
    -- /// Decreases clause to ensure recursive function termination
    -- /// decrease.len() == 0 means no decreases clause
    -- /// decrease.len() >= 1 means list of expressions, interpreted in lexicographic order
    decrease: Array Expr
    -- /// If Expr is true for the arguments to the function,
    -- /// the function is defined according to the function body and the decreases clauses must hold.
    -- /// If Expr is false, the function is uninterpreted, the body and decreases clauses are ignored.
    decrease_when: Option Expr
deriving ToJson, FromJson, Repr, Inhabited

-- /// Function, including signature and body
structure Theorem where
    -- /// Name of function
    name: Path
    -- /// Type parameters to generic functions
    -- /// (for trait methods, the trait parameters come first, then the method parameters)
    typ_params: Idents
    -- /// Function parameters
    params: Binders Typ
    -- /// Preconditions (requires for proof/exec functions, recommends for spec functions)
    require: Array Expr
    -- /// Postconditions (proof/exec functions only)
    ensure: Array Expr
deriving ToJson, FromJson, Repr, Inhabited

inductive Decl
| Defn : Defn → Decl
| Theorem : Theorem → Decl
deriving ToJson, FromJson, Repr, Inhabited
