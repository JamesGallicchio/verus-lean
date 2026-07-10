# verus-lean

`verus-lean` translates [Verus](https://github.com/verus-lang/verus) programs
and their verification conditions into Lean, using a
[fork of Verus](https://github.com/ccodel/verus/tree/boogie) that exports them
as JSON. It supports two translation targets:

- **Verus → Lean**: a direct Lean encoding.
- **Verus → Boole**: a lowering of Verus's intermediate representation (VLIR)
  to [Strata](https://github.com/strata-org/Strata)'s *Boole* dialect.

A Boole program's verification conditions can be discharged in two ways:

- **An external SMT solver.** cvc5 or z3, invoked through `Strata.Boole.verify`.
  This is the path the `--verify` test stage uses.
- **Within Lean.** Strata emits the verification conditions as Lean goals with
  the `gen_smt_vcs_boole` tactic, which you then close using tactics such as
  `grind`. This produces a Lean-checked proof and lets you discharge obligations
  interactively, without trusting an external solver.

## Setup

`verus-lean` builds with [Lake](https://github.com/leanprover/lean4/tree/master/src/lake)
(Lean's build tool) and expects a couple of sibling repositories in the same
workspace directory.

### 1. Clone the repositories

Clone this repository and its two siblings into one workspace directory:

```bash
# This repository.
git clone -b boole https://github.com/ChengZ3/verus-boogie.git

# The Strata Boole dialect and verifier.
git clone -b dalek-lite-benchmarks https://github.com/kondylidou/Strata-Boole.git

# The Verus export front end.
git clone -b boogie https://github.com/ccodel/verus.git
```

Your workspace should look like this:

```text
<workspace>/
  verus-boogie/     # this repository
  Strata-Boole/
  verus/            # only needed for the Verus export step
```

> **Temporary.** The `Strata-Boole` clone above uses the fork branch
> `dalek-lite-benchmarks` of
> [`kondylidou/Strata-Boole`](https://github.com/kondylidou/Strata-Boole), which
> carries a few changes still under review upstream. Once they merge, switch this
> clone to [`strata-org/Strata-Boole`](https://github.com/strata-org/Strata-Boole)
> (`main`).

You do not need to clone Strata itself. It is a separate repository from
Strata-Boole, and the `Strata-Boole` branch above declares it as a Git
dependency, so Lake fetches it during the build from
[`strata-org/Strata`](https://github.com/strata-org/Strata) (`main`).

### 2. Build

From this repository's root:

```bash
lake build
```

Lake fetches and compiles the whole dependency graph (Strata, Strata-DDM, and
Strata-Boole), then `verus-lean`. The compiled binary is at:

```
.lake/build/bin/verus-lean
```

For convenience you may symlink it to the repository root:

```bash
ln -s .lake/build/bin/verus-lean verus-lean
```

### Optional Strata patches for full verification

Building `verus-lean`, generating Boole translations, and verifying them all
work against upstream Strata `main` with no extra steps. Almost every test
verifies this way, so most readers can skip this section.

Two narrow cases are the exception. Each needs a small addition to Strata that is
not yet upstream, and both affect only the verification stage:

- **128-bit bitvector operations**, for programs that use `u128` or `i128`, such
  as the `b1` benchmarks. Without them, verifying such a program reports an
  unknown `Bv128.*` operator. Generating the translation still works.
- **The cvc5 `--enum-inst` flag**, for a handful of enum-heavy tests. Without it
  they report `unknown` rather than passing. They still do not fail, and no
  other test is affected.

Only if you need one of these cases, put a copy of Strata at `../Strata` and
apply the two additions to it. Then add a local override to this repository's
`lakefile.lean`:

```
require Strata from "../Strata"
```

Because it lives in the root package, this requirement takes precedence over the
one Strata-Boole pulls from Git, so Lake builds against your local copy. Run
`lake update Strata` so the manifest records the change, and leave both edits
uncommitted.

## Usage

Everything runs through one driver, `tests/run_tests.sh`. It chains the pipeline
(Verus export, Boole generation, verification), finds the sibling repositories,
and starts from whichever stage the input calls for. From the repository root:

```bash
./tests/run_tests.sh [options] [target]
```

### Stages

- `--verus`: export a Verus `.rs` file to JSON.
- `--boole`: generate a Boole `.boole.st` file and a Lean file that embeds it for verification.
- `--verify`: run Strata Boole verification on that Lean file.
- `--all`: run all three (export, generate, verify).

### Targets

The target is a single input file:

- `.rs`: a Verus source file. `--boole` exports it to JSON, then generates Boole.
- `.json`: an exported JSON file. `--boole` generates Boole from it directly,
  without re-running export.
- `.lean`: the Lean file `--boole` writes, embedding the Boole program for verification. `--verify` runs it.
- no target: each stage runs over the bundled fixtures under `tests/`, which is
  how the regression suite runs.

With `--verify`, an `.rs` or `.json` target selects the matching Lean file rather
than regenerating it.

### Other options

- `--out <path>`: output path for a single-target `--boole` run.
- `--solver <name>`: SMT solver for `--verify` (`cvc5` or `z3`; default `cvc5`).
- `--verbose`: show full output, including every proof obligation during
  `--verify`.
- `--synth-disable <names>`: turn off selected synthesized verification aids
  during generation.

### Examples

```bash
# Full pipeline, from a Verus source file:
./tests/run_tests.sh --all tests/VerusFiles/FindMax.rs

# Generate Boole from an already-exported JSON file:
./tests/run_tests.sh --boole tests/JSONFilesBoogie/vlir-tests/FindMax/FindMax.json

# Write the Boole output to a custom path:
./tests/run_tests.sh --boole tests/VerusFiles/FindMax.rs --out /tmp/FindMax.boole.st
```

Generated files are written to `tests/BooleFiles` (Boole source, `.boole.st`) and
`tests/BoolePrograms` (each program embedded in a Lean file for verification).

### Repository paths

Each stage relies on a different part of the workspace from [Setup](#setup):

- `--verus` reads the Verus fork at `../verus`.
- `--boole` needs only the built `verus-lean` binary.
- `--verify` runs `lake env lean` inside `../Strata-Boole`. The proof builds
  against whatever Strata that package resolves (`strata-org` main by default;
  see [Optional Strata patches](#optional-strata-patches-for-full-verification)).

Override any path with an environment variable:

```bash
VERUS_DIR=/path/to/verus \
STRATA_BOOLE_DIR=/path/to/Strata-Boole \
  ./tests/run_tests.sh --all path/to/file.rs
```

The individual binaries and the output directory can be overridden too
(`VERUS_BIN`, `VERUS_LEAN`, `BOOLE_DIR`).

### Calling the translator directly

`run_tests.sh` invokes the `verus-lean` binary for the JSON to Boole step. You
can run that step on its own, for example to print to stdout or to script it
outside the test tree:

```bash
.lake/build/bin/verus-lean boole <input.json> [output.boole.st]
```

With no output path it prints to stdout. This is the same translation `--boole`
performs; the driver additionally writes the Lean file and runs the export and
verify stages around it.

### Regenerating Lean from changed sources

An experimental Python helper, `vl.py`, drives the Verus fork end to end and
re-syncs declarations when the source `.rs` file changes:

```bash
python vl.py <input.rs> <output.lean>
```

The re-sync is experimental, so keep backups of any hand-written Lean.

## How the Boole translation works

### The pipeline

A Verus program reaches a solver in four stages. `tests/run_tests.sh` runs them
in order, and **each stage writes an artifact you can inspect**:

```
 .rs ──(1) Verus export──▶ .json      ──(2) parse──▶ VLIR Decls
                                                         │
                          .boole.st ◀──(4) render── BooleDDM ◀──(3) translate
                              │
                              └──▶ Lean file ──▶ Strata (SMT solver or Lean tactics)
```

1. **Verus export.** The Verus fork (`../verus`, `boogie` branch) writes each
   source file's intermediate representation (VLIR) as JSON. This step lives in
   Verus, not here; the `--verus` stage runs it. The output goes to
   `tests/JSONFilesBoogie/<suite>/<name>/<name>.json`, plus `<name>_*.json`
   shards for multi-module programs.

2. **Parse.** `VerusLean/VLIR/Parser.lean` reads that JSON into the VLIR data
   types in `VerusLean/VLIR/Defs.lean`: the type `Typ`, expression `Exp`, and
   statement `Stm`, plus the top-level `Decl` (cases like `specFn`, `proofFn`, `execFn`,
   `struct`, and `enum`). The entry point is `Decls.fromFile?`.

3. **Translate.** `VerusLean/VLIR/Boole/Translate.lean` lowers the VLIR
   declarations to Strata's `BooleDDM` commands. `declsToBooleProgram`
   orchestrates it:
   1. resolve trait-method calls to their concrete impls (`TraitResolve.lean`)
      and build the associated-type resolution;
   2. build the layout maps (wrapper, struct, and enum field info) that length
      contracts recurse through;
   3. prune dead declarations (`Pruning.lean`): erased `Vec` and allocator
      types, unreferenced impl accessors, abstract trait methods, and unused
      `vstd` specs;
   4. lower each declaration (`declToBoole`), delegating to the helper modules
      below;
   5. emit the support declarations and synthesized helpers gathered during
      lowering, ahead of the user decls that reference them.

4. **Render.** `VerusLean/VLIR/Boole/Emit.lean` turns the commands into
   `.boole.st` text, prepending only the `nat`, `Seq`, and `Vec` preludes the
   program actually uses (planned in `Prelude.lean`, loaded in `Main.lean`). The
   result is embedded in a Lean file under `tests/BoolePrograms/` (via
   `#strata ... #end`, with a `Strata.Boole.verify` call), which `Strata-Boole`
   checks with an SMT solver.

`Main.lean` is the command-line entry point and drives stages 2 through 4 for
the `boole` command.

### Where each concern lives (`VerusLean/VLIR/Boole/`)

| concern | modules |
|---|---|
| BooleDDM builders | `Builder.lean` (types, expressions, statements), `Bld.lean` (short-alias re-export of `Builder`) |
| translation state | `Context.lean` (variable scopes, layout maps, `SynthConfig`) |
| naming | `Names.lean` (source names to Boole identifiers) |
| numeric domains | `Coercions.lean`, `Cast.lean`, `IntPromotion.lean` (classify and coerce between `int`, `nat`, and bitvector), `Inference.lean` (type and bit-width inference), `Ops.lean` (per-operator builders) |
| pre-lowering rewrites | `Normalize.lean` (temp inlining, substitution), `ForLoop.lean` (loop recovery), `Projection.lean` (struct and enum field layouts), `Reveal.lean` (`reveal` to an assumed equality) |
| local-variable analysis | `Locals.lean` |
| trait handling | `TraitResolve.lean` (trait-method call resolution) |
| synthesized proof aids | `Synth.lean` (array-length and loop-bound facts), `VariantReqs.lean` (variant preconditions) |
| dead-code pruning | `Pruning.lean` |
| support declarations and preludes | `Support.lean`, `SupportEmit.lean`, `Prelude.lean` |
| final assembly and rendering | `Emit.lean` (assembles commands, resolves names, loads preludes, renders `.boole.st`) |

The Verus-to-Lean target, as opposed to Boole, uses `Elab.lean`, `Delab.lean`,
and `Pp.lean` instead of the `Boole/` tree.

### Debugging a translation error

The stage that fails tells you where to look. Work from the outside in,
inspecting the artifact each stage produced.

1. **Find the failing stage.** Run `tests/run_tests.sh` and read the step banner
   (`Step 1: Verus -> JSON`, `Step 2: JSON -> Boole`, `Step 3: Strata Boole
   verify`), or run one stage at a time with `--verus`, `--boole`, or `--verify`.

2. **Open the artifact for that stage.** Every intermediate is on disk:
   - exported JSON: `tests/JSONFilesBoogie/<suite>/<name>/<name>.json`
   - generated Boole program: `tests/BooleFiles/<suite>/<name>.boole.st`
   - the program embedded in Lean: `tests/BoolePrograms/<suite>/<name>.lean`

3. **Match the error to a stage and a module.**
   - A **Verus export error** (from `../verus`) points at the Rust source or the
     Verus fork, not verus-lean.
   - A **parse error** (`unexpected …`, or a missing JSON key) means the JSON
     contains a VLIR shape `Parser.lean` does not handle yet. Extend
     `Parser.lean`, and `Defs.lean` if a new node is needed.
   - A **translation error** (a Lean `throw`, such as `unsupported binary op …`
     or `tuple projection out of range`) comes from `Translate.lean` or a helper.
     The message names the concern: a numeric-domain mismatch points at the
     `Inference`/`Coercions` group, a struct or enum field projection at
     `Projection.lean`, and a loop at `ForLoop.lean`.
   - A **Strata type-check error at verify** (`Undeclared type or category …`,
     `Unknown variable …`, or `… shadows an enclosing block`) means an emitted construct
     references a name that was never declared (a pruning or naming bug), or
     collides with a reserved one. Open the `.boole.st` at the reported line and
     trace the symbol back to the declaration that emitted it.
   - A **verification `unknown` or timeout** comes from the SMT solver, not the
     translation. The obligation may be genuinely hard, or it may be missing a
     synthesized aid such as a length precondition or a loop bound (see
     `Synth.lean`). Re-run `--verify --verbose` to see which obligation is open.

4. **Reduce it.** Regenerate a single file with
   `./tests/run_tests.sh --boole tests/VerusFiles/<name>.rs` and read its
   `.boole.st` directly. The line and column in a Strata error map to a concrete
   emitted command, which you can trace back to the VLIR `Decl` and the
   translator code that produced it.

## Contributors

- Cheng Zhang, research engineer at Stanford University (chengz3@stanford.edu)
- Cayden Codel, PhD student at Carnegie Mellon University (ccodel@andrew.cmu.edu)
- James Gallicchio, PhD student at Carnegie Mellon University (jgallicc@andrew.cmu.edu)
