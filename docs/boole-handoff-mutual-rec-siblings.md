# Boole handoff — Mutual-rec sibling bvars

## Summary

`lowerPureFuncDef` doesn't push the previously-defined siblings of a
`command_recfndefs` block onto the bvar scope when lowering each body.
The DDM parser already binds earlier siblings as bvars (via
`@[declareFn]`), so any reference to a sibling function from inside a
`rec function` body fails to resolve at lowering time.

## Symptom

Mutually-recursive function definitions like

```
rec function is_even (n : nat) : bool { if n == 0 then true else is_odd (n - 1) };
rec function is_odd  (n : nat) : bool { if n == 0 then false else is_even (n - 1) };
```

raise "unknown identifier" / "free variable" errors when the body of one
function references the other.  The single-fn recursive case (a fn
calling itself) works; only mutual recursion is broken.

## Affected files

- `Strata/Languages/Boole/Verify.lean` — `lowerPureFuncDef` and the
  call site that processes `command_recfndefs`

## Reference patch

Our local branch carries the change as part of commit `f9387373d`.  The
shape is:

```diff
 private def lowerPureFuncDef
     ...
-    (inline : Bool) : TranslateM Core.Function := do
+    (inline : Bool)
+    (siblings : Array Core.Expression.Expr := #[]) : TranslateM Core.Function := do
+  -- `siblings` carries preceding-function `opExpr`s for the mutually-recursive
+  -- case. The DDM parser (via `@[declareFn]`) binds earlier siblings as bvars
+  -- when elaborating each function body in a `command_recfndefs` block, so we
+  -- must push them onto the bvar scope before lowering `body` / `pres`.
+  -- Mirrors Core's `translateRecFnDecl` (see that function's `bbindings`).
   withTypeBVars tys do
+    withBVarExprs siblings do
       ...
```

The caller threads in the previously-lowered siblings as `Core.Expression.Expr`
values so each subsequent body sees them in scope.

## Test idea

```
rec function is_even (n : nat) : bool { if nat_to_int(n) == 0 then true  else is_odd (n - 1) };
rec function is_odd  (n : nat) : bool { if nat_to_int(n) == 0 then false else is_even(n - 1) };

procedure check () returns () {
  assert is_even (4 : nat);
}
```

Today this fails to elaborate because `is_odd` is unbound inside
`is_even`'s body.

## Notes

- The Core-side `translateRecFnDecl` already does the equivalent thing
  via its `bbindings` parameter — so the reference for "what's the right
  set of bvars" is right there.
- Single-fn recursive definitions still work without the patch because
  they re-bind their own name implicitly; the patch is only needed for
  blocks of length ≥ 2.
