use vstd::prelude::*;

verus! {

//////////////////////////////////////////////////////////////////
//
//  Definition of our Abstract Syntax Trees (ASTs)
//
//////////////////////////////////////////////////////////////////

// #[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum Op {
    Plus,
    Sub,
    Times,
    Leq,
    Eq,
}

// #[derive(Debug, Clone, Eq, Hash, PartialEq)]
struct Variable {
    // name: String,
    name: &'static str,
}

// #[derive(Clone, PartialEq, Eq)]
enum Expr {
    Bool(bool),
    Int(int),
    Var(Variable),
    // use a pointer to an Expr because size of a recursive type must be finite
    BinaryOp(Op, Box<Expr>, Box<Expr>),
}

// #[derive(Clone, PartialEq, Eq)]
enum Command {
    Noop,
    Assign(Variable, Expr),
    Concat(Box<Command>, Box<Command>),
    IfThenElse(Expr, Box<Command>, Box<Command>),
    While(Expr, Box<Command>),
}

//////////////////////////////////////////////////////////////////
//
//  Semantics of Expressions
//  (i.e., What does an expression _mean_?)
//
//////////////////////////////////////////////////////////////////

// Expressions evaluate to either a Boolean or an integer value
// #[derive(Clone, PartialEq, Eq)]
enum Value {
    B(bool),
    I(int),
}

// The Result type lets us indicate whether evaluating an
// expression fails or succeeds with a particular value
// (see EvalExpr for examples of when it might fail)
// #[derive(Clone, PartialEq, Eq)]
enum EResult {
    EFail,
    ESuccess(Value),
}

// The store (or memory) maps variables to their values
type Store = Map<Variable, Value>;

// Semantics of expression evaluation
spec fn EvalExpr(e: Box<Expr>, store: &Store) -> EResult 
    decreases e,
{
    match *e {
        Expr::Bool(b) => EResult::ESuccess(Value::B(b)),
        Expr::Int(i)  => EResult::ESuccess(Value::I(i)),
        Expr::Var(v)  => {
            if (*store).dom().contains(v) {
                EResult::ESuccess((*store)[v])
            } else {
                EResult::EFail
            }
        }
        Expr::BinaryOp(op, left, right) => {
            let left = EvalExpr(left, store);
            let right = EvalExpr(right, store);
            match (left, right) {
                (EResult::EFail, _) | (_, EResult::EFail) => EResult::EFail,
                (EResult::ESuccess(Value::I(i1)), EResult::ESuccess(Value::I(i2))) => {
                    match op {
                        Op::Plus  => EResult::ESuccess(Value::I(i1 + i2)),
                        Op::Sub   => EResult::ESuccess(Value::I(i1 - i2)),
                        Op::Times => EResult::ESuccess(Value::I(i1 * i2)),
                        Op::Leq   => EResult::ESuccess(Value::B(i1 <= i2)),
                        Op::Eq    => EResult::ESuccess(Value::B(i1 == i2)),
                    }
                }
                _ => EResult::EFail,
            }
        }
    }          
}

proof fn ExprExamples() {
    let x : Variable = Variable{name: "x"};
    let e : Expr = Expr::BinaryOp(Op::Plus, Box::new(Expr::Int(5)), Box::new(Expr::Var(x)));
    let s : Store = map![x => Value::I(2)];
    
    // Example 1
    assert(EvalExpr(e->1, &s) is ESuccess); // helper assert
    assert(EvalExpr(e->2, &s) is ESuccess); // helper assert
    assert(EvalExpr(Box::new(e), &s) is ESuccess);
    assert(EvalExpr(Box::new(e), &s) == EResult::ESuccess(Value::I(7)));

    // Example 2
    let e : Expr = Expr::BinaryOp(Op::Leq, Box::new(Expr::Var(x)), Box::new(Expr::Int(3)));
    let s : Store = map![x => Value::I(2)];
    // assert(EvalExpr(e->1, &s) is ESuccess); // helper assert
    assert(EvalExpr(e->2, &s) is ESuccess); // helper assert
    assert(EvalExpr(Box::new(e), &s) is ESuccess);
    assert(EvalExpr(Box::new(e), &s) == EResult::ESuccess(Value::B(true)));

    // Example 3
    let s : Store = map![x => Value::I(4)];
    assert(EvalExpr(e->1, &s) is ESuccess); // helper assert
    assert(EvalExpr(e->2, &s) is ESuccess); // helper assert
    assert(EvalExpr(Box::new(e), &s) is ESuccess);
    assert(EvalExpr(Box::new(e), &s) == EResult::ESuccess(Value::B(false)));

    // Example 4
    let s : Store = map![];
    assert(EvalExpr(e->1, &s) is EFail); // helper assert
    assert(EvalExpr(Box::new(e), &s) is EFail);

    // Example 5
    let e : Expr = Expr::BinaryOp(Op::Times, Box::new(Expr::Int(3)), Box::new(Expr::Bool(true)));
    assert(EvalExpr(e->1, &s) is ESuccess); // helper assert
    assert(EvalExpr(e->2, &s) is ESuccess); // helper assert
    assert(EvalExpr(Box::new(e), &s) is EFail);
}

//////////////////////////////////////////////////////////////////
//
//  Semantics of Commands
//
//////////////////////////////////////////////////////////////////

enum CResult {
    Timeout,
    Fail,
    Success{s:Store},
}

struct State {
    fuel: nat,
    store: Store,
}

spec fn EvalCommand(s: &State, c: Box<Command>) -> CResult
    decreases s.fuel, c
{
    if s.fuel == 0 {
        CResult::Timeout
    } else {
        match *c {
            Command::Noop => CResult::Success{s: s.store},
            Command::Assign(v, e) => { // variable := e
                match EvalExpr(Box::new(e), &s.store) {
                    EResult::EFail => CResult::Fail,
                    EResult::ESuccess(val) => {
                        CResult::Success{s: s.store.insert(v, val)}
                    }
                }
            }
            Command::Concat(c0, c1) => { // c0 ; c1
                let result0 = EvalCommand(s, c0);
                match result0 {
                    CResult::Timeout => CResult::Timeout,
                    CResult::Fail => CResult::Fail,
                    CResult::Success{s: store0} => {
                        EvalCommand(&State {fuel: s.fuel, store: store0}, c1)
                    }
                }
            }
            Command::IfThenElse(cond, ifTrue, ifFalse) => { // if cond then { ifTrue } else { ifFalse }
                let value = EvalExpr(Box::new(cond), &s.store);
                match value {
                    EResult::EFail => CResult::Fail,
                    EResult::ESuccess(Value::I(_)) => CResult::Fail, // Unlike C, we do not allow integers to be used as Boolean conditions
                    EResult::ESuccess(Value::B(b)) => 
                        if b {
                            EvalCommand(s, ifTrue)
                        } else {
                            EvalCommand(s, ifFalse)
                        }
                }
            }
            Command::While(cond, body) => {
                let value = EvalExpr(Box::new(cond), &s.store);
                match value {
                    EResult::EFail => CResult::Fail,
                    EResult::ESuccess(Value::I(_)) => CResult::Fail, // Unlike C, we do not allow integers to be used as Boolean conditions
                    EResult::ESuccess(Value::B(b)) => 
                        if !b {
                            // The while loop is complete
                            CResult::Success{s: s.store}
                        } else {
                            // Otherwise, execute the body, and then re-evaluate the while loop code (c)
                            EvalCommand(&State {fuel: (s.fuel - 1) as nat, store: s.store}, Box::new(Command::Concat(body, c)))
                        }
                }
            }
        }
    }
}

proof fn CommandExamples()
{
    let x : Variable = Variable{name: "x"};
    let store : Store = map![x => Value::I(2)];
    let s : State = State{fuel: 1 as nat, store: store};
    
    // Example 0: Noop has no effect
    let cr = EvalCommand(&s, Box::new(Command::Noop));
    assert(cr is Success && cr->s == store);

    // Example 1: Assignment successfully mutates the store
    let c = Box::new(Command::Assign(x, Expr::Int(732)));
    let cr = EvalCommand(&s, c);
    assert(cr is Success && cr->s == map![x => Value::I(732)]);

    // Example 2: Concatenation behaves sequentially
    let c0 = Box::new(Command::Assign(x, Expr::Int(732)));
    let c1 = Box::new(Command::Assign(x, Expr::Int(335)));
    let c = Box::new(Command::Concat(c0, c1));
    // assert(EvalCommand(&s, c0) is Success && EvalCommand(&s, c1) is Success); // helper assert
    assert(EvalCommand(&s, c0) matches CResult::Success{s: store0} 
        && EvalCommand(&State {fuel: s.fuel, store: store0}, c1) is Success); // helper assert
    let cr = EvalCommand(&s, c);
    assert(cr is Success && cr->s == map![x => Value::I(335)]);

    // Example 3: IfThenElse behaves as expected
    let c = Box::new(Command::IfThenElse(Expr::Bool(true), c0, c1));
    // assert(EvalCommand(&s, c0) is Success); // helper assert
    let cr = EvalCommand(&s, c);
    assert(cr is Success && cr->s == map![x => Value::I(732)]);

    let c = Box::new(Command::IfThenElse(Expr::Bool(false), c0, c1));
    assert(EvalCommand(&s, c1) is Success); // helper assert
    let cr = EvalCommand(&s, c);
    assert(cr is Success && cr->s == map![x => Value::I(335)]);

    // Example 4: We can prove things about what gets printed
    // omitted for now
}


//////////////////////////////////////////////////////////////////
//
//  Typing Rules
//
//////////////////////////////////////////////////////////////////

// Mini-C only supports two types: integers and Booleans
enum Type {
    TInt,
    TBool,
}

type Declarations = Map<Variable, Type>;

spec fn ExprHasType(d:Declarations, e:Expr, t:Type) -> bool 
    decreases e
{
    match e {
        Expr::Bool(_) => t is TBool,
        Expr::Int(_) => t is TInt,
        Expr::Var(v) => if d.contains_key(v) { d[v] == t } else { false },
        Expr::BinaryOp(op, lhs, rhs) => {
            ExprHasType(d, *lhs, Type::TInt) && ExprHasType(d, *rhs, Type::TInt) &&
            match op {
                Op::Plus | Op::Sub | Op::Times => t is TInt,
                Op::Leq | Op::Eq => t is TBool,
            }
        }
    }
}

spec fn CommandWellTyped(d:Declarations, c:Command) -> bool 
    decreases c
{
    match c {
        Command::Noop => true,
        Command::Assign(v, e) => if d.contains_key(v) { ExprHasType(d, e, d[v]) } else { false },
        Command::Concat(c0, c1) => CommandWellTyped(d, *c0) && CommandWellTyped(d, *c1),
        Command::IfThenElse(cond, ifTrue, ifFalse) => {
            ExprHasType(d, cond, Type::TBool) &&
            CommandWellTyped(d, *ifTrue) && CommandWellTyped(d, *ifFalse)
        },
        Command::While(cond, body) => {
            ExprHasType(d, cond, Type::TBool) && CommandWellTyped(d, *body)
        },
    }
}

spec fn StoreWellTyped(d:Declarations, s:Store) -> bool 
{
    forall|v| { d.contains_key(v) ==> 
        s.contains_key(v) && 
        match d[v] {
            Type::TInt => s[v] is I,
            Type::TBool => s[v] is B,
        }
    }
}

// Helper Lemma #1:
//   Evaluating a well-typed expression using a well-typed store
//   will always succeed
proof fn WellTypedExprSuccess(d:Declarations, s:Store, e:Expr, t:Type)
    requires
        StoreWellTyped(d, s),
        ExprHasType(d, e, t),
    ensures
    // CZ: not sure why Verus does not prove this automatically like Dafny does
        EvalExpr(Box::new(e), &s) is ESuccess,
        t is TBool ==> EvalExpr(Box::new(e), &s)->0 is B,
        t is TInt ==> EvalExpr(Box::new(e), &s)->0 is I,
    decreases e,
{
    match e {
        Expr::Bool(_) | Expr::Int(_) | Expr::Var(_)  => 
            assert(EvalExpr(Box::new(e), &s) is ESuccess), // Verus automatically proves these cases
        Expr::BinaryOp(op, lhs, rhs) => {
            assert(ExprHasType(d, *lhs, Type::TInt) && ExprHasType(d, *rhs, Type::TInt));
            WellTypedExprSuccess(d, s, *lhs, Type::TInt);
            WellTypedExprSuccess(d, s, *rhs, Type::TInt);
        }
    }
}

// Helper Lemma #2:
//   Evaluating a well-typed command using a well-typed store
//   will either time out (e.g., imagine a well-typed infinite loop),
//   or evaluated successfully and produce a well-typed store
proof fn WellTypedCommandSuccess(d:Declarations, s:State, c:Command)
    requires
        StoreWellTyped(d, s.store),
        CommandWellTyped(d, c),
    ensures
        EvalCommand(&s, Box::new(c)) is Timeout ||
        (EvalCommand(&s, Box::new(c)) is Success && StoreWellTyped(d, EvalCommand(&s, Box::new(c))->s)),
    decreases s.fuel, c,
{
    if s.fuel > 0 {
        match c {
            Command::Noop => { // Verus automatically proves this case
            }
            Command::Assign(v, e) => {
                WellTypedExprSuccess(d, s.store, e, d[v]);
            }
            Command::Concat(c0, c1) => {
                WellTypedCommandSuccess(d, s, *c0);
                let cr = EvalCommand(&s, c0);
                if cr is Success {
                    WellTypedCommandSuccess(d, State {fuel: s.fuel, store: cr->s}, *c1);
                }
            }
            Command::IfThenElse(cond, ifTrue, ifFalse) => {
                WellTypedExprSuccess(d, s.store, cond, Type::TBool);
                WellTypedCommandSuccess(d, s, *ifTrue);
                WellTypedCommandSuccess(d, s, *ifFalse);
            }
            Command::While(cond, body) => {
                WellTypedExprSuccess(d, s.store, cond, Type::TBool);
                WellTypedCommandSuccess(d, State {fuel: (s.fuel - 1) as nat, store: s.store}, 
                                       Command::Concat(body, Box::new(c)));
            }
        }
    }
}

// Our top level type-safety theorem:
//   If evaluating a well-typed command using a well-typed store
//   does not time out, then it must succeed (i.e., it doesn't fail),
//   and it produces a well-typed store
proof fn TypeSafety(d:Declarations, s:State, c:Command) by (lean_proof)
    requires
        StoreWellTyped(d, s.store),
        CommandWellTyped(d, c),
        !(EvalCommand(&s, Box::new(c)) is Timeout),
    ensures
        EvalCommand(&s, Box::new(c)) is Success && 
        StoreWellTyped(d, EvalCommand(&s, Box::new(c))->s),
{
    // Invoke our helper lemma (#2)
    WellTypedCommandSuccess(d, s, c);
}

fn main() {
  assert(true);
}

}
