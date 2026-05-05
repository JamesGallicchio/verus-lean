# Boole handoff — Datatype-decl symbol registration

## Summary

`registerCommandSymbols` for `.command_datatypes` registers only one
slot per datatype (the datatype name itself) and does **not** register
the constructors, tester aliases, or destructors that the declaration
introduces.  Anything that references a constructor like
`Tuple_ctor_2(...)`, a tester like `Option..isSome(...)`, or a
destructor like `Tuple.._0(...)` therefore fails verification with

```
No free variables are allowed here! Free Variables: [<ctor>]
```

## Symptom

Tests that exercise tuples, option types, or any user-declared
`datatype` (e.g. `adts_eq.rs`, `structural.rs`) fail to verify even
though they elaborate cleanly.  In the SHA-256 compression test, the
former presence of `Slice_Iter_iter (T)` as an emitted datatype was
hitting the same path.

## Affected files

- `Strata/Languages/Boole/Verify.lean` — `registerCommandSymbols`,
  specifically the `.command_datatypes` arm

## Reference patch

Our local branch carries the change across commits `f9387373d` (added
the helper) and `7de89b75b` (reintroduced the call site after a
cherry-pick dropped it).  The combined shape is:

```lean
private def registerCommandSymbols (cmd : BooleDDM.Command SourceRange) : List Bool :=
  let registerDatatypeDecl (decl : BooleDDM.DatatypeDecl SourceRange) : List Bool :=
    match decl with
    | .datatype_decl _ _ _ ctors =>
      let ctorSymbols :=
        (constructorListToList ctors).foldr
          (fun ctor acc =>
            match ctor with
            | .constructor_mk _ _ ⟨_, fields?⟩ =>
              let fieldCount :=
                match fields? with
                | none => 0
                | some ⟨_, fs⟩ => fs.size
              -- Datatype commands elaborate into:
              --   1. the datatype name itself
              --   2. each constructor
              --   3. each tester alias (`T..isCtor`)
              --   4. each safe destructor
              --   5. each unsafe destructor
              ([true, true] ++ List.replicate fieldCount true ++ List.replicate fieldCount true) ++ acc)
          []
      false :: ctorSymbols
  match cmd with
  ...
  | .command_datatypes _ ⟨_, decls⟩ =>
      decls.toList.foldr (fun decl acc => registerDatatypeDecl decl ++ acc) []
  ...
```

Slot counts per declaration: `1` (datatype name) + Σ over constructors
of `2 + 2 × fieldCount` (constructor + tester + safe/unsafe destructors
per field).

## Test idea

Two minimal cases:

```
datatype Pair (A : Type, B : Type) {
  Pair_ctor_2(_0 : A, _1 : B)
};

procedure use_ctor () returns () {
  var p : (Pair int int);
  p := Pair_ctor_2(1, 2);
  assert Pair.._0(p) == 1;
}
```

Today this fails with the "no free variables allowed" error on
`Pair_ctor_2` (and on the destructor `Pair.._0` after the constructor
issue is fixed).

A second case exercising testers:

```
datatype Maybe (A : Type) {
  Maybe_None,
  Maybe_Some(_0 : A)
};

procedure check (m : Maybe int) returns () {
  if Maybe..isMaybe_Some(m) {
    assert Maybe..Maybe_Some_0(m) >= 0;
  }
}
```

## Notes

- Without the helper, the original site was `decls.toList.map (fun _ => false)`
  — one slot per datatype declaration, regardless of arity.  All the
  constructor / tester / destructor symbols leaked through as unbound
  free variables.
- The cherry-pick incident from commit `7de89b75b` is a useful
  reminder: the `command_datatypes` arm is the only call site that
  needs to use `registerDatatypeDecl`; if a future merge resolves the
  conflict in favour of "no per-ctor slots", verification regresses
  silently for any test using user-declared datatypes.
- Consider whether tester aliases and unsafe destructors should be
  registered as `false` (type/decl symbols) instead of `true` (op
  symbols).  Our patch uses `true` uniformly per slot; that matches
  empirical behaviour but a Boole maintainer may want to refine the
  classification.
