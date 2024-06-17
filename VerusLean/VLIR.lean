import VerusLean.Upstream

/-! A copy of the VIR AST from Verus. -/

/-!
//! The VIR-AST Abstract Syntax Tree
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! VIR-AST follows the structure of Rust-HIR, but omits features that are not needed
//! for verification.
-/

open Lean (Json ToJson FromJson)

def Any := Lean.Json
deriving Lean.ToJson, FromJson, ToString
instance : Repr Any where
  reprPrec _ _ := "_"

def Ident := String
deriving ToJson, FromJson, Repr

def Idents := Array Ident
deriving ToJson, FromJson, Repr

structure Binder (A : Type) where
  name: Ident
  a: A
deriving ToJson, FromJson, Repr

abbrev Binders (A) := Array (Binder A)

/-- A fully-qualified name, such as a module name, function name, or datatype name -/
structure Path where
  /-- None for local crate -/
  krate: Option Ident
  segments: Idents
deriving ToJson, FromJson, Repr

inductive VarIdentDisambiguate
  -- AIR names that don't derive from rustc's names:
| AirLocal
  -- rustc's parameter unique id comes from the function body; no body means no id:
| NoBodyParam
  -- TypParams are normally Idents, but sometimes we mix TypParams into lists of VarIdents:
| TypParamBare
| TypParamSuffixed
| TypParamDecorated
  -- Fields are normally Idents, but sometimes we mix field names into lists of VarIdents:
| Field
| RustcId : USize → VarIdentDisambiguate
  -- We track whether the variable is SST/AIR statement-bound or expression-bound,
  -- to help drop unnecessary ids from expression-bound variables
| VirRenumbered (is_stmt: Bool) (does_shadow: Bool) (id: UInt64)
  -- Some expression-bound variables don't need an id
| VirExprNoNumber
  -- We rename parameters to VirParam if the parameters don't conflict with each other
| VirParam
  -- Recursive definitions have an extra copy of the parameters
| VirParamRecursion : USize → VarIdentDisambiguate
  -- Capture-avoiding substitution creates new names:
| VirSubst : UInt64 → VarIdentDisambiguate
| VirTemp : UInt64 → VarIdentDisambiguate
| ExpandErrorsDecl : UInt64 → VarIdentDisambiguate
deriving ToJson, FromJson, Repr

/-- A local variable name, possibly renamed for disambiguation -/
def VarIdent := Ident × VarIdentDisambiguate
deriving Repr
instance : ToJson VarIdent where
  toJson := fun (id,dis) => .arr #[Lean.toJson id, Lean.toJson dis]
instance : FromJson VarIdent where
  fromJson? j := (do
    let arr ← j.getArr?
    if h : arr.size = 2 then
      let id ← Lean.fromJson? arr[0]
      let dis ← Lean.fromJson? arr[1]
      return (id, dis)
    else
      throw s!"expected array of length 2, got {arr}"
  ).mapError (fun s => s!"varident: {s}\n{j}")


structure VarBinder (A: Type) where
  name: VarIdent
  a: A
deriving ToJson, FromJson, Repr

def VarBinders A := Array (VarBinder A)
instance [ToJson A] : ToJson (VarBinders A) := inferInstanceAs (ToJson (Array _))
instance [FromJson A] : FromJson (VarBinders A) := inferInstanceAs (FromJson (Array _))
instance [Repr A] : Repr (VarBinders A) := inferInstanceAs (Repr (Array _))

/-- Static function identifier -/
structure Fun where
  /-- Path of function -/
  path: Path
deriving ToJson, FromJson, Repr

/-- Describes what access other modules have to a function, datatype, etc. -/
structure Visibility where
  /--
  None for pub
  Some(path) means visible to path and path's descendents
  -/
  restricted_to: Option Path
deriving ToJson, FromJson, Repr

/-- Describes whether a variable, function, etc. is compiled or just used for verification -/
inductive Mode where
  /-- Ghost (not compiled), used to represent specifications (requires, ensures, invariant) -/
  | Spec
  /-- Ghost (not compiled), used to represent proofs of that specifications are satisfied -/
  | Proof
  /-- Non-ghost (compiled code) -/
  | Exec
deriving ToJson, FromJson, Repr


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
deriving ToJson, FromJson, Repr

inductive ImplPath
  /-- the usual `impl X for Trait`. The 'Path' is to the 'impl' block -/
  | TraitImplPath : Path → ImplPath
  /-- Declaration of a function `f` which conceptually implements a trait bound
     `FnDef(f) : FnOnce` -/
  | FnDefImplPath : Fun → ImplPath
deriving ToJson, FromJson, Repr

/-- Path of each impl that is used to satisfy a trait bound when instantiating the type parameter
This is used to name the "dictionary" that is (conceptually) passed along with the
type argument (see recursive_types.rs) -/
-- REVIEW: should trait_typ_args also have ImplPaths?
def ImplPaths := Array ImplPath
deriving ToJson, FromJson, Repr

/-- Rust type, but without Box, Rc, Arc, etc. -/
inductive Typ
  /-- Bool, Int, Datatype are translated directly into corresponding SMT types (they are not SMT-boxed) -/
  | Bool
  | Int : IntRange → Typ
  /-- UTF-8 character type -/
  | Char
  /-- Tuple type (t1, ..., tn).  Note: ast_simplify replaces Tuple with Datatype. -/
  | Tuple : Array Typ → Typ
  /--
    `FnSpec` type (TODO rename from 'Lambda' to just 'FnSpec')
    (t1, ..., tn) -> t0. -/
  | Lambda : Array Typ → Typ → Typ
  /-- Executable function types (with a requires and ensures) -/
  | AnonymousClosure : Array Typ → Typ → USize → Typ
  /-- Corresponds to Rust's FnDef type
    Typs are generic type args
    If Fun is a trait function, then the Option<Fun> has the statically resolved
    function if it exists. Similar to ImplPaths, this is technically redundant
    (because it follows from the types), but it is not easy to compute without
    storing it here. We need it because it is useful for determining which
    FnDef axioms to introduce. -/
  | FnDef : Fun → Array Typ → Option Fun → Typ
  /-- Datatype (concrete or abstract) applied to type arguments -/
  | Datatype : Path → Array Typ → ImplPaths → Typ
  /-- StrSlice type. Currently the vstd StrSlice struct is "seen" as this type
    despite the fact that it is in fact a datatype -/
  | StrSlice
  | Array : Typ → Typ → Typ
  | Slice : Typ → Typ
  /-- Type parameter (inherently SMT-boxed, and cannot be unboxed) -/
  | TypParam : Ident → Typ
  /-- Projection such as <D as T<S>>::X or <A as T>::X (SMT-boxed, and can sometimes be unboxed) -/
  | Projection
        (trait_typ_args: Array Typ)
        (trait_path: Path)
        (name: Ident)
  /-- Type of type identifiers -/
  | TypeId
  /-- Const integer type argument (e.g. for array sizes) -/
  | ConstInt : Int → Typ
  /- Left out: AIR constructor used internally -/
  | Decorate : Any → Typ → Typ
deriving FromJson, ToJson, Repr

/-
inductive TriggerAnnotation {
    -- /// Automatically choose triggers for the expression containing this annotation,
    -- /// with no diagnostics printed
    AutoTrigger,
    AllTriggers,
    -- /// Each trigger group is named by either Some integer, or the unnamed group None.
    -- /// (None is just another name; it is no different from an integer-named group.)
    -- /// Example: #[trigger] expr is translated into Trigger(None) applied to expr
    -- /// Example: #[trigger(1, 2, 3)] expr is translated into three Trigger ops wrapped around expr
    -- ///   (Trigger(Some(1)), Trigger(Some(2)), Trigger(Some(3)))
    Trigger(Option<UInt64>),
}

-- /// Operations on Ghost and Tracked
#[derive(Copy, Clone, Debug, Serialize, Deserialize, Hash, PartialEq, Eq, ToDebugSNode)]
inductive ModeCoercion {
    -- /// Mutable borrows (Ghost::borrow_mut and Tracked::borrow_mut) are treated specially by
    -- /// the mode checker when checking assignments.
    BorrowMut,
    -- /// All other cases are treated uniformly by the mode checker based on their op/from/to-mode.
    -- /// (This includes Ghost::borrow, Tracked::get, etc.)
    Other,
}
-/

-- /// Primitive 0-argument operations
inductive NullaryOpr
    -- /// convert a const generic into an expression, as in fn f<const N: USize>() -> USize { N }
  | ConstGeneric : Typ → NullaryOpr
    -- /// predicate representing a satisfied trait bound T(t1, ..., tn) for trait T
  | TraitBound : Path → Array Typ → NullaryOpr
    -- /// predicate representing a type equality bound T<t1, ..., tn, X = typ> for trait T
  | TypEqualityBound : Path → Array Typ → Ident → Typ → NullaryOpr
    -- /// A failed InferSpecForLoopIter subexpression
  | NoInferSpecForLoopIter
deriving ToJson, FromJson, Repr

/-- Primitive unary operations
 (not arbitrary user-defined functions -- these are represented by ExprX::Call) -/
inductive UnaryOp where
    /-- Boolean not -/
    | Not
    /-- bitwise not -/
    | BitNot
    /-
    -- /// Mark an expression as a member of an SMT quantifier trigger group.
    -- /// Each trigger group becomes one SMT trigger containing all the expressions in the trigger group.
    Trigger(TriggerAnnotation),
    -- /// Force integer value into range given by IntRange (e.g. by using mod)
    Clip { range: IntRange, truncate: Bool },
    -- /// Operations that coerce from/to builtin::Ghost or builtin::Tracked
    CoerceMode { op_mode: Mode, from_mode: Mode, to_mode: Mode, kind: ModeCoercion },
    -- /// Internal consistency check to make sure finalize_exp gets called
    -- /// (appears only briefly in SST before finalize_exp is called)
    MustBeFinalized,
    -- /// We don't give users direct access to the "height" function and Height types.
    -- /// However, it's useful to be able to trigger on the "height" function
    -- /// when using HeightCompare.  We manage this by having triggers.rs convert
    -- /// HeightCompare triggers into HeightTrigger, which is eventually translated
    -- /// into direct calls to the "height" function in the triggers.
    HeightTrigger,
    -- /// Used only for handling builtin::strslice_len
    StrLen,
    -- /// Used only for handling builtin::strslice_is_ascii
    StrIsAscii,
    -- /// Used only for handling casts from chars to ints
    CharToInt,
    -- /// Given an exec/proof expression used to construct a loop iterator,
    -- /// try to infer a pure specification for the loop iterator.
    -- /// Evaluate to Some(spec) if successful, None otherwise.
    -- /// (Note: this is just used as a hint for loop invariants;
    -- /// regardless of whether it is Some(spec) or None, it should not affect soundness.)
    -- /// For an exec/proof expression e, the spec s should be chosen so that the value v
    -- /// that e evaluates to is immutable and v == s, where v may contain local variables.
    -- /// For example, if v == (n..m), then n and m must be immutable local variables.
    InferSpecForLoopIter { print_hint: Bool },
    -- /// May need coercion after casting a type argument
    CastToInteger,
    -/
deriving ToJson, FromJson, Repr

inductive VariantCheck
  | None
  -- Recommends,
  | Yes
deriving ToJson, FromJson, Repr

inductive IntegerTypeBoundKind
  | UnsignedMax
  | SignedMin
  | SignedMax
  | ArchWordBits
deriving ToJson, FromJson, Repr

structure FieldOpr where
  datatype: Path
  variant: Ident
  field: Ident
  get_variant: Bool
  check: VariantCheck
deriving ToJson, FromJson, Repr

/-- More complex unary operations (requires Clone rather than Copy)
  (Below, "boxed" refers to boxing types in the SMT encoding, not the Rust Box type) -/
inductive UnaryOpr : Type
  /-- coerce Typ --> Boxed(Typ) -/
  | Box : Typ → UnaryOpr
  /-- coerce Boxed(Typ) --> Typ -/
  | Unbox : Typ → UnaryOpr
  /-- satisfies type invariant for Typ
    (should only be used when sst_to_air::typ_invariant returns Some(_)) -/
  | HasType : Typ → UnaryOpr
  /-- Test whether expression is a particular variant of a datatype -/
  | IsVariant (datatype: Path) (variant: Ident)
    -- /// Read .0, .1, etc. from tuple (Note: ast_simplify replaces this with Field)
  | TupleField (tuple_arity: USize) (field: USize)
    -- /// Read field from variant of datatype
  | Field : FieldOpr → UnaryOpr
    -- /// Bounded integer bounds. The argument is the arch word bits (16, 32, etc.)
    -- /// So e.g., IntegerTypeBound(SignedMax) applied to 8 would give 127
    -- /// The 'ArchWordBits' gives the word size in bits (ignore the argument).
    -- /// This can return any integer type, but that integer type needs to be large enough
    -- /// to hold the result.
    -- /// Mode is the minimum allowed mode (e.g., Spec for spec-only, Exec if allowed in exec).
  | IntegerTypeBound : IntegerTypeBoundKind → Mode → UnaryOpr
    -- /// Custom diagnostic message
  | CustomErr : String → UnaryOpr
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
deriving ToJson, FromJson, Repr

-- /// Bitwise operation
inductive BitwiseOp
  | BitXor
  | BitAnd
  | BitOr
  | Shr
  | Shl
deriving ToJson, FromJson, Repr


inductive InequalityOp
    -- /// IntRange::Int <=
  | Le
    -- /// IntRange::Int >=
  | Ge
    -- /// IntRange::Int <
  | Lt
    -- /// IntRange::Int >
  | Gt
deriving ToJson, FromJson, Repr

inductive ChainedOp
  | Inequality : InequalityOp → ChainedOp
  | MultiEq
deriving ToJson, FromJson, Repr

-- /// Primitive binary operations
-- /// (not arbitrary user-defined functions -- these are represented by ExprX::Call)
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
    -- /// the is_smaller_than builtin, used for decreases (true for <, false for ==)
  --| HeightCompare { strictly_lt: Bool, recursive_function_field: Bool }
    -- /// SMT equality for any type -- two expressions are exactly the same value
    -- /// Some types support compilable equality (Mode == Exec); others only support spec equality (Mode == Spec)
  | Eq : Mode → BinaryOp
    -- /// not Eq
  | Ne
    -- /// arithmetic inequality
  | Inequality : InequalityOp → BinaryOp
    -- /// IntRange operations that may require overflow or divide-by-zero checks
  | Arith : ArithOp → Mode → BinaryOp
    -- /// Bit Vector Operators
    -- /// mode=Exec means we need overflow-checking
  | Bitwise : BitwiseOp → Mode → BinaryOp
    -- /// Used only for handling builtin::strslice_get_char
  | StrGetChar
deriving ToJson, FromJson, Repr

-- /// More complex binary operations (requires Clone rather than Copy)
inductive BinaryOpr
    -- /// extensional equality ext_equal (true ==> deep extensionality)
  | ExtEq : Bool → Typ → BinaryOpr
deriving ToJson, FromJson, Repr

inductive MultiOp
  | Chained : Array ChainedOp → MultiOp
deriving ToJson, FromJson, Repr

-- /// Primitive constant values
inductive Constant
    -- /// true or false
  | Bool : Bool → Constant
    -- /// integer of arbitrary size
  | Int : Int → Constant
    -- /// Hold generated string slices in here
  | StrSlice : String → Constant
    -- Hold unicode values here
    -- The standard library doesn't use string constants and i'm not sure how they are encoded by serde
  --| Char : Char → Constant
deriving ToJson, FromJson, Repr

/-
inductive Pattern : Type
    -- /// _
    -- /// True if this is implicitly added from a ..
  | Wildcard (_ : Bool)
    -- /// x or mut x
  | Var (name: VarIdent) (mutable: Bool)
  | Binding
      (name: VarIdent)
      (mutable: Bool)
      (sub_pat: Pattern)
    -- /// Note: ast_simplify replaces this with Constructor
  | Tuple (_ : Array Pattern)
    -- /// Match constructor of datatype Path, variant Ident
    -- /// For tuple-style variants, the fields are named "_0", "_1", etc.
    -- /// Fields can appear **in any order** even for tuple variants.
  | Constructor (_ : Path) (_1 : Ident) (_ : Array (Binder Pattern))
  | Or (_ : PatternX) (_: Pattern)
    -- /// Matches something equal to the value of this expr
    -- /// This only supports literals and consts, so we don't need to worry
    -- /// about side-effects, binding order, etc.
  --| Expr (_ : Expr)
    -- /// `e1 <= x <= e2` or `e1 <= x < e2`
    -- /// The start of the range is always inclusive (<=)
    -- /// The end of the range may be inclusive (<=) or exclusive (<),
    -- /// as given by the InequalityOp argument.
  -- | Range (_ : Option Expr) (_ : Option (Expr × InequalityOp))


-- /// Patterns for match expressions
def Patterns := Array Pattern

-- /// Arms of match expressions
pub type Arm = Arc<Spanned<ArmX>>;
pub type Arms = Arc<Vec<Arm>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
structure ArmX {
    -- /// pattern
    pub pattern: Pattern,
    -- /// "if" condition on a case
    pub guard: Expr,
    -- /// expression or statement the executes when case matches
    pub body: Expr,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, ToDebugSNode)]
inductive LoopInvariantKind {
    -- /// holds at beginning of loop
    InvariantExceptBreak,
    -- /// holds at beginning of loop and after loop exit (including breaks)
    InvariantAndEnsures,
    -- /// holds at loop exit (including breaks)
    Ensures,
}

pub type LoopInvariants = Arc<Vec<LoopInvariant>>;
#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode)]
structure LoopInvariant {
    pub kind: LoopInvariantKind,
    pub inv: Expr,
}
-/

inductive BuiltinSpecFun
    -- Note that this now applies to any supported function type, e.g., FnDef types,
    -- not just "closure" types. TODO rename?
  | ClosureReq
  | ClosureEns
deriving ToJson, FromJson, Repr


inductive AutospecUsage
    -- /// This function should be lowered by autospec iff the
    -- /// target function has an autospec attribute.
  | IfMarked
    -- /// Do not apply autospec. (This might be because we already applied it during lowering,
    -- /// or because it doesn't apply to this function.)
  | Final
deriving ToJson, FromJson, Repr


inductive CallTargetKind
    -- /// Statically known function
  | Static
    -- /// Dynamically dispatched method.  Optionally specify the statically resolved target if known.
  | Method : (Option (Fun × Array Typ × ImplPaths)) → CallTargetKind
deriving ToJson, FromJson, Repr

inductive CallTarget
    -- /// Regular function, passing some type arguments
  | Fun : CallTargetKind → Fun → Array Typ → ImplPaths → AutospecUsage → CallTarget
    -- /// Call a dynamically computed FnSpec (no type arguments allowed),
    -- /// where the function type is specified by the GenericBound of typ_param.
  --| FnSpec : Expr → CallTarget
  | BuiltinSpecFun : BuiltinSpecFun → Array Typ → ImplPaths → CallTarget
deriving ToJson, FromJson, Repr

inductive VarAt
  | Pre
deriving ToJson, FromJson, Repr


inductive InvAtomicity
  | Atomic
  | NonAtomic
deriving ToJson, FromJson, Repr

inductive AssertQueryMode
  | NonLinear
  | BitVector
deriving ToJson, FromJson, Repr

-- /// Computation mode for assert_by_compute
inductive ComputeMode
    -- /// After simplifying an expression as far as possible,
    -- /// pass the remainder as an assertion to Z3
  | Z3
    -- /// Asserted expression must simplify all the way to True
  | ComputeOnly
deriving ToJson, FromJson, Repr

inductive Quant.Inner
  | Forall
  | Exists
deriving ToJson, FromJson, Repr

structure Quant where
  quant : Quant.Inner
deriving ToJson, FromJson, Repr

inductive ExprX : Type
    -- /// Constant
  | Const : Constant → ExprX
    -- /// Local variable as a right-hand side
  | Var : VarIdent → ExprX
    -- /// Local variable as a left-hand side
  | VarLoc : VarIdent → ExprX
    -- /// Local variable, at a different stage (e.g. a mutable reference in the post-state)
  | VarAt : VarIdent → VarAt → ExprX
    -- /// Use of a const variable.  Note: ast_simplify replaces this with Call.
  | ConstVar : Fun → AutospecUsage → ExprX
    -- /// Use of a static variable.
  | StaticVar : Fun → ExprX
    -- /// Mutable reference (location)
  | Loc : Spanned ExprX → ExprX
    -- /// Call to a function passing some expression arguments
  | Call : CallTarget → Array (Spanned ExprX) → ExprX
    -- /// Note: ast_simplify replaces this with Ctor
  | Tuple : Array (Spanned ExprX) → ExprX
    -- /// Construct datatype value of type Path and variant Ident,
    -- /// with field initializers Binders<Expr> and an optional ".." update expression.
    -- /// For tuple-style variants, the fields are named "_0", "_1", etc.
    -- /// Fields can appear **in any order** even for tuple variants.
  | Ctor : Path → Ident → Array (Binder (Spanned ExprX))  → Option (Spanned ExprX) → ExprX
    -- /// Primitive 0-argument operation
  | NullaryOpr : NullaryOpr → ExprX
    -- /// Primitive unary operation
  | Unary : UnaryOp → (Spanned ExprX) → ExprX
    -- /// Special unary operator
  | UnaryOpr : UnaryOpr → (Spanned ExprX) → ExprX
    -- /// Primitive binary operation
  | Binary : BinaryOp → (Spanned ExprX) → (Spanned ExprX) → ExprX
    -- /// Special binary operation
  | BinaryOpr : BinaryOpr → (Spanned ExprX) → (Spanned ExprX) → ExprX
    -- /// Primitive multi-operand operation
  | Multi : MultiOp → Array (Spanned ExprX) → ExprX
    -- /// Quantifier (forall/exists), binding the variables in Binders, with body ExprX
  | Quant : Quant → VarBinders Typ → (Spanned ExprX) → ExprX
    -- /// Specification closure
  | Closure : VarBinders Typ → (Spanned ExprX) → ExprX
    -- /// Executable closure
  | ExecClosure
        (params: VarBinders Typ)
        (body: (Spanned ExprX))
        (requires: Array (Spanned ExprX))
        (ensures: Array (Spanned ExprX))
        (ret: VarBinder Typ)
        -- /// The 'external spec' is an Option because it gets filled in during
        -- /// ast_simplify. It contains the assumptions that surrounding context
        -- /// can assume about a closure object after it is created.
        (external_spec: Option (VarIdent × (Spanned ExprX)) )
    -- /// Array literal (can also be used for sequence literals in the future)
  | ArrayLiteral : Array (Spanned ExprX) → ExprX
    -- /// Executable function (declared with 'fn' and referred to by name)
  | ExecFnByName : Fun → ExprX
    -- /// Choose specification values satisfying a condition, compute body
  | Choose
        (params: VarBinders Typ)
        (cond: (Spanned ExprX))
        (body: (Spanned ExprX))
    -- /// Manually supply triggers for body of quantifier
  | WithTriggers
        (triggers: Array (Array (Spanned ExprX)) )
        (body: (Spanned ExprX))
    -- /// Assign to local variable
    -- /// init_not_mut = true ==> a delayed initialization of a non-mutable variable
  | Assign
        (init_not_mut: Bool)
        (lhs: (Spanned ExprX))
        (rhs: (Spanned ExprX))
        (op: Option BinaryOp)
    -- /// Reveal definition of an opaque function with some integer fuel amount
  | Fuel: Fun → UInt32 → Bool → ExprX
    -- /// Reveal a string
  | RevealString : String → ExprX
    -- /// Assert or assume
  | AssertAssume (is_assume: Bool) (expr: (Spanned ExprX))
    -- /// Assert-forall or assert-by statement
  | AssertBy
        (vars: VarBinders Typ)
        (require: (Spanned ExprX))
        (ensure: (Spanned ExprX))
        (proof: (Spanned ExprX))
    -- /// `assert_by` with a dedicated prover option (nonlinear_arith, bit_vector)
  | AssertQuery
        (requires: Array (Spanned ExprX))
        (ensures: Array (Spanned ExprX))
        (proof: (Spanned ExprX))
        (mode: AssertQueryMode)
    -- /// Assertion discharged via computation
  | AssertCompute : (Spanned ExprX) → ComputeMode → ExprX
    -- /// If-else
  | If: (Spanned ExprX) → (Spanned ExprX) → Option (Spanned ExprX) → ExprX
    -- /// Match (Note: ast_simplify replaces Match with other expressions)
  | Match: (Spanned ExprX) → Any → ExprX
    -- /// Loop (either "while", cond = Some(...), or "loop", cond = None), with invariants
  | Loop
        (loop_isolation: Bool)
        (is_for_loop: Bool)
        (label: Option String)
        (cond: Option (Spanned ExprX))
        (body: (Spanned ExprX))
        --(invs: LoopInvariants)
        (decrease: Array (Spanned ExprX))
    -- /// Open invariant
  | OpenInvariant: (Spanned ExprX) → VarBinder Typ → (Spanned ExprX) → InvAtomicity → ExprX
    -- /// Return from function
  | Return: Option (Spanned ExprX) → ExprX
    -- /// break or continue
  | BreakOrContinue
        (label: Option String)
        (is_break: Bool)
    -- /// Enter a Rust ghost block, which will be erased during compilation.
    -- /// In principle, this is not needed, because we can infer which code to erase using modes.
    -- /// However, we can't easily communicate the inferred modes back to rustc for erasure
    -- /// and lifetime checking -- rustc needs syntactic annotations for these, and the mode checker
    -- /// needs to confirm that these annotations agree with what would have been inferred.
  | Ghost
        (alloc_wrapper: Bool)
        (tracked: Bool)
        (expr: (Spanned ExprX))
    -- /// Sequence of statements, optionally including an expression at the end
  -- | Block: Stmts → Option (Spanned ExprX) → ExprX
deriving ToJson, FromJson, Repr

abbrev Expr := Spanned ExprX

/-
-- /// Statement, similar to rustc_hir::Stmt
pub type Stmt = Arc<Spanned<StmtX>>;
pub type Stmts = Arc<Vec<Stmt>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
inductive StmtX {
    -- /// Single expression
    Expr(Expr),
    -- /// Declare a local variable, which may be mutable, and may have an initial value
    -- /// The declaration may contain a pattern;
    -- /// however, ast_simplify replaces all patterns with PatternX::Var
    -- /// (The mode is only allowed to be None for one special case; see modes.rs)
    Decl { pattern: Pattern, mode: Option<Mode>, init: Option<Expr> },
}-/

-- /// Function parameter
structure ParamX where
    name: VarIdent
    typ: Typ
    mode: Mode
    -- /// An &mut parameter
    is_mut: Bool
    -- /// If the parameter uses a Ghost(x) or Tracked(x) pattern to unwrap the value, this is
    -- /// the mode of the resulting unwrapped x variable (Spec for Ghost(x), Proof for Tracked(x)).
    -- /// We also save a copy of the original wrapped name for lifetime_generate
    unwrapped_info: Option (Mode × VarIdent)
deriving ToJson, FromJson, Repr

abbrev Param := Spanned ParamX

/-
pub type GenericBound = Arc<GenericBoundX>;
pub type GenericBounds = Arc<Vec<GenericBound>>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode)]
inductive GenericBoundX {
    -- /// Implemented trait T(t1, ..., tn) where t1...tn usually contain some type parameters
    -- REVIEW: add ImplPaths here?
    Trait(Path, Typs),
    -- /// An equality bound for associated type X of trait T(t1, ..., tn),
    -- /// written in Rust as T<t1, ..., tn, X = typ>
    TypEquality(Path, Typs, Ident, Typ),
}

-- /// When instantiating type S<A> with A = T in a recursive type definition,
-- /// is T allowed to include the one of recursively defined types?
-- /// Example:
-- ///   enum Foo { Rec(S<Box<Foo>>), None }
-- ///   enum Bar { Rec(S<Box<Bar>>) }
-- ///   (instantiates A with recursive type Box<Foo> or Box<Bar>)
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Clone, Copy, PartialEq, Eq)]
inductive AcceptRecursiveType {
    -- /// rejects the Foo example above
    -- /// (because A may occur negatively in S)
    Reject,
    -- /// accepts the Foo example above because the occurrence is in Rec,
    -- /// which is not the ground variant for Foo (None is the ground variant for Foo),
    -- /// but rejects Bar because Rec is the ground variant for Bar (since there is no None variant)
    -- /// (because A occurs only strictly positively in S, but may occur in S's ground variant)
    RejectInGround,
    -- /// accepts both Foo and Bar
    -- /// (because A occurs only strictly positively in S, and does not occur in S's ground variant)
    Accept,
}
-- /// Each type parameter is (name: Ident, GenericBound, AcceptRecursiveType)
pub type TypPositives = Arc<Vec<(Ident, AcceptRecursiveType)>>;

pub type FunctionAttrs = Arc<FunctionAttrsX>;
#[derive(Debug, Serialize, Deserialize, ToDebugSNode, Default, Clone)]
structure FunctionAttrsX {
    -- /// Erasure and lifetime checking based on ghost blocks
    pub uses_ghost_blocks: Bool,
    -- /// Inline spec function for SMT
    pub inline: Bool,
    -- /// List of functions that this function wants to view as opaque
    pub hidden: Arc<Vec<Fun>>,
    -- /// Create a global axiom saying forall params, require ==> ensure
    pub broadcast_forall: Bool,
    -- /// In triggers_auto, don't use this function as a trigger
    pub no_auto_trigger: Bool,
    -- /// Custom error message to display when a pre-condition fails
    pub custom_req_err: Option<String>,
    -- /// When used in a ghost context, redirect to a specified spec function
    pub autospec: Option<Fun>,
    -- /// Verify using bitvector theory
    pub bit_vector: Bool,
    -- /// Is atomic (i.e., can be inside an invariant block)
    pub atomic: Bool,
    -- /// Verify non_linear arithmetic using Singular
    pub integer_ring: Bool,
    -- /// This is a proof of termination for another spec function
    pub is_decrease_by: Bool,
    -- /// In a spec function, check the body for violations of recommends
    pub check_recommends: Bool,
    -- /// set option smt.arith.nl=true
    pub nonlinear: Bool,
    -- /// Use a dedicated Z3 process for this single query
    pub spinoff_prover: Bool,
    -- /// Memoize function call results during interpretation
    pub memoize: Bool,
    -- /// override default rlimit
    pub rlimit: Option<f32>,
    -- /// does this function take zero args (this is useful to keep track
    -- /// of because we add a dummy arg to zero functions)
    pub print_zero_args: Bool,
    -- /// is this a method, i.e., written with x.f() syntax? useful for printing
    pub print_as_method: Bool,
    pub prophecy_dependent: Bool,
    -- /// broadcast proof from size_of global
    pub size_of_broadcast_proof: Bool,
}

-- /// Function specification of its invariant mask
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
inductive MaskSpec {
    InvariantOpens(Exprs),
    InvariantOpensExcept(Exprs),
}-/

inductive FunctionKind
  | Static
    -- /// Method declaration inside a trait
  | TraitMethodDecl
        (trait_path: Path)
    -- /// Method implementation inside an impl, implementing a trait method for a trait for a type
  | TraitMethodImpl
        -- /// Fun declared by trait for this method
        (method: Fun)
        -- /// Path of the impl (e.g. "impl2") that contains the method implementation
        (impl_path: Path)
        (trait_path: Path)
        (trait_typ_args: Array Typ)
        -- /// If Some, inherit default method body from function in the trait:
        (inherit_body_from: Option Fun)
    -- /// These should get demoted into Static functions in `demote_foreign_traits`.
    -- /// This really only exists so that we can check the trait really is foreign.
  | ForeignTraitMethodImpl
        (method: Fun)
        (impl_path: Path)
        (trait_path: Path)
        (trait_typ_args: Array Typ)
deriving ToJson, FromJson, Repr


-- /// Function, including signature and body
structure Function where
    -- /// Name of function
    name: Fun
    -- /// exec functions are compiled, proof/spec are erased
    -- /// exec/proof functions can have requires/ensures, spec cannot
    -- /// spec functions can be used in requires/ensures, proof/exec cannot
    mode: Mode
    -- /// Type parameters to generic functions
    -- /// (for trait methods, the trait parameters come first, then the method parameters)
    typ_params: Idents
    -- /// Type bounds of generic functions
    --typ_bounds: GenericBounds
    -- /// Function parameters
    params: Array Param
    -- /// Return value (unit return type is treated specially; see FunctionX::has_return in ast_util)
  --  ret: Param
    -- /// Preconditions (requires for proof/exec functions, recommends for spec functions)
  --  require: Array Expr
    -- /// Postconditions (proof/exec functions only)
  --  ensure: Array Expr
    -- /// Decreases clause to ensure recursive function termination
    -- /// decrease.len() == 0 means no decreases clause
    -- /// decrease.len() >= 1 means list of expressions, interpreted in lexicographic order
  --  decrease: Array Expr
    -- /// If Expr is true for the arguments to the function,
    -- /// the function is defined according to the function body and the decreases clauses must hold.
    -- /// If Expr is false, the function is uninterpreted, the body and decreases clauses are ignored.
  --  decrease_when: Option Expr
deriving ToJson, FromJson

#eval show IO Unit from do
  let contents ← IO.FS.readFile "verus/source/vstd.json"
  let tyjs ← IO.ofExcept <| do
    (← Json.parse contents).getArr?
  for tyj in tyjs do
    try
      let _f : Function ← IO.ofExcept (Lean.fromJson? tyj)
      pure ()
    catch e =>
      IO.println e
      IO.println <| ← IO.ofExcept do
        let arr ← (← tyj.getObjVal? "require").getArr?
        let a := arr[0]!
        let b : Spanned Any ← Lean.fromJson? a
        let c ← (← b.x.getObjVal? "Binary").getArr?
        let d := c[1]!
        let e : Spanned Any ← Lean.fromJson? d
        let f := e.x
        let g ← (← f.getObjVal? "Binary").getArr?
        let h : Spanned Any ← Lean.fromJson? g[1]!
        let i := h.x
        return (repr <| Lean.fromJson? (α := ExprX) i, toString i)
      break
  return

/-
#[derive(Debug, Serialize, Deserialize, Clone, ToDebugSNode, Copy)]
inductive ItemKind {
    Function,
    -- /// This function is actually a const declaration;
    -- /// we treat const declarations as functions with 0 arguments, having mode == Spec.
    -- /// However, if ret.x.mode != Spec, there are some differences: the const can dually be used as spec,
    -- /// and the body is restricted to a subset of expressions that are spec-safe.
    Const,
    -- /// Static is kind of similar to const, in that we treat it as a 0-argument function.
    -- /// The main difference is what happens when you reference the static or const.
    -- /// For a const, it's as if you call the function every time you reference it.
    -- /// For a static, it's as if you call the function once at the beginning of the program.
    -- /// The difference is most obvious when the item of a type that is not Copy.
    -- /// For example, if a const/static has type PCell, then:
    -- ///  - If it's a const, it will get a different id() every time it is referenced from code
    -- ///  - If it's a static, every use will have the same id()
    -- /// This initially seems a bit paradoxical; const and static can only call 'const' functions,
    -- /// so they can only be deterministic, right? But for something like cell, the 'id'
    -- /// (the nondeterministic part) is purely ghost.
    Static,
}

pub type RevealGroup = Arc<Spanned<RevealGroupX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure RevealGroupX {
    -- /// Name of the function that is used internally to represent the group.
    -- /// This is used, for example, to create a Node::Fun(name) for the group.
    -- /// Note that there is no FunctionX for the group, though.
    pub name: Fun,
    -- /// Access control (public/private)
    pub visibility: Visibility,
    -- /// Owning module
    pub owning_module: Option<Path>,
    -- /// If true, then prune away group unless either the module that contains the group is used.
    -- /// (Without this, importing vstd would recursively reach and encode all the
    -- /// broadcast_forall declarations in all of vstd, defeating much of the purpose of prune.rs.)
    pub prune_unless_this_module_is_used: Bool,
    -- /// If Some(crate_name), this group is revealed by default for crates that import crate_name.
    -- /// No more than one such group is allowed in each crate.
    pub broadcast_use_by_default_when_this_crate_is_imported: Option<Ident>,
    -- /// All the subgroups or functions included in this group
    pub members: Arc<Vec<Fun>>,
}

-- /// Single field in a variant
pub type Field = Binder<(Typ, Mode, Visibility)>;
-- /// List of fields in a variant
-- /// For tuple-style variants, the fields appear in order and are named "0", "1", etc.
-- /// For struct-style variants, the fields may appear in any order
pub type Fields = Binders<(Typ, Mode, Visibility)>;

#[derive(Clone, Copy, Debug, Serialize, Deserialize, ToDebugSNode)]
inductive CtorPrintStyle {
    Tuple,  -- actual tuple (a, b)
    Parens, -- tuple style: Ctor(a, b)
    Braces, -- struct: Ctor { a: ... }
    Const,  -- just Ctor
}

pub type Variants = Arc<Vec<Variant>>;

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure Variant {
    pub name: Ident,
    pub fields: Fields,
    pub ctor_style: CtorPrintStyle,
}

#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
inductive DatatypeTransparency {
    Never,
    WhenVisible(Visibility),
}

-- /// struct or enum
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure DatatypeX {
    pub path: Path,
    -- /// Similar to FunctionX proxy field.
    -- /// If this datatype is declared via a proxy (a type labeled external_type_specification)
    -- /// then this points to the proxy.
    -- /// e.g., we might have,
    -- ///   path = core::option::Option
    -- ///   proxy = vstd::std_specs::core::ExOption
    pub proxy: Option<Spanned<Path>>,
    pub owning_module: Option<Path>,
    pub visibility: Visibility,
    pub transparency: DatatypeTransparency,
    pub typ_params: TypPositives,
    pub typ_bounds: GenericBounds,
    pub variants: Variants,
    pub mode: Mode,
    -- /// Generate ext_equal lemmas for datatype
    pub ext_equal: Bool,
}
pub type Datatype = Arc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

pub type Trait = Arc<Spanned<TraitX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure TraitX {
    pub name: Path,
    pub visibility: Visibility,
    -- REVIEW: typ_params does not yet explicitly include Self (right now, Self is implicit)
    pub typ_params: TypPositives,
    pub typ_bounds: GenericBounds,
    pub assoc_typs: Arc<Vec<Ident>>,
    pub assoc_typs_bounds: GenericBounds,
    pub methods: Arc<Vec<Fun>>,
}

-- /// impl<typ_params> trait_name<trait_typ_args[1..]> for trait_typ_args[0] { type name = typ; }
pub type AssocTypeImpl = Arc<Spanned<AssocTypeImplX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure AssocTypeImplX {
    pub name: Ident,
    -- /// Path of the impl (e.g. "impl2") that contains "type name = typ;"
    pub impl_path: Path,
    pub typ_params: Idents,
    pub typ_bounds: GenericBounds,
    pub trait_path: Path,
    pub trait_typ_args: Typs,
    pub typ: Typ,
    -- /// Paths of the impls that are used to satisfy the bounds on the associated type
    pub impl_paths: ImplPaths,
}

pub type TraitImpl = Arc<Spanned<TraitImplX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure TraitImplX {
    -- /// Path of the impl (e.g. "impl2")
    pub impl_path: Path,
    -- typ_params of impl (unrelated to typ_params of trait)
    pub typ_params: Idents,
    pub typ_bounds: GenericBounds,
    pub trait_path: Path,
    pub trait_typ_args: Typs,
    pub trait_typ_arg_impls: Arc<Spanned<ImplPaths>>,
    pub owning_module: Option<Path>,
}

#[derive(Clone, Debug, Hash, Serialize, Deserialize, ToDebugSNode, PartialEq, Eq)]
inductive WellKnownItem {
    DropTrait,
}

pub type ModuleReveals = Arc<Spanned<Vec<Fun>>>;

pub type Module = Arc<Spanned<ModuleX>>;
#[derive(Clone, Debug, Serialize, Deserialize, ToDebugSNode)]
structure ModuleX {
    pub path: Path,
    -- add attrs here
    pub reveals: Option<ModuleReveals>,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, ToDebugSNode)]
inductive ArchWordBits {
    Either32Or64,
    Exactly(u32),
}

impl ArchWordBits {
    pub fn min_bits(&self) -> u32 {
        match self {
            ArchWordBits::Either32Or64 => 32,
            ArchWordBits::Exactly(v) => *v,
        }
    }
    pub fn num_bits(&self) -> Option<u32> {
        match self {
            ArchWordBits::Either32Or64 => None,
            ArchWordBits::Exactly(v) => Some(*v),
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
structure Arch {
    pub word_bits: ArchWordBits,
}

-- /// An entire crate
pub type Krate = Arc<KrateX>;
#[derive(Clone, Debug, Serialize, Deserialize)]
structure KrateX {
    -- /// All functions in the crate, plus foreign functions
    pub functions: Vec<Function>,
    -- /// All reveal_groups in the crate
    pub reveal_groups: Vec<RevealGroup>,
    -- /// All datatypes in the crate
    pub datatypes: Vec<Datatype>,
    -- /// All traits in the crate
    pub traits: Vec<Trait>,
    -- /// Every impl in the crate of a trait
    pub trait_impls: Vec<TraitImpl>,
    -- /// All associated type impls in the crate
    pub assoc_type_impls: Vec<AssocTypeImpl>,
    -- /// List of all modules in the crate
    pub modules: Vec<Module>,
    -- /// List of all 'external' functions in the crate (only useful for diagnostics)
    pub external_fns: Vec<Fun>,
    -- /// List of all 'external' types in the crate (only useful for diagnostics)
    pub external_types: Vec<Path>,
    -- /// Map rustc-based internal paths to friendlier names for error messages
    pub path_as_rust_names: Vec<(Path, String)>,
    -- /// Arch info
    pub arch: Arch,
}
-/
