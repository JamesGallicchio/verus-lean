# verus-lean: A Verus-Lean connection

The Lean backend to a [verus fork](https://github.com/ccodel/verus/tree/boogie)
that allows for the export of verus definitions and verification conditions to Lean.

This repository now supports two main translation paths:
- `Verus -> Lean`
- `Verus -> Boole` (direct VLIR -> BooleDDM)

## Building

All building/compiling is done at the root level of the project,
unless otherwise indicated.

If you haven't set up the project yet, run
```
lake update          # Installs Lean and its dependencies
lake exe cache get   # Downloads pre-compiled .olean files
```

After, and for all subsequent builds, run
```
lake build
```

The compiled binary can be found at `.lake/build/bin/verus-lean`.

(I find it helpful to symlink the `bin/` folder at root level: `ln -s .lake/build/bin bin`,
or perhaps even better, `ln -s .lake/build/bin/verus-lean verus-lean`.)

## Running

You can run the compiled `verus-lean` binary directly:
```
./lake/build/bin/verus-lean boole <path/to/serialized_verus.json> [path/to/output.boole.st]
```
Alternatively, you can use a Python script that works in concert with my verus fork.
(The script assumes that this fork is on your `$PATH`, or is (symlinked) at the root level of the project.)

To use this script, run
```
python vl.py <path/to/verus.rs> <path/to/lean/output.lean>
```

One benefit of the Python script is that it (semi-)intelligently updates the declarations if the source verus `.rs` file changes.
This replacement is very experimental, so be careful not to lose your work in Lean!

## Testing (`tests/run_tests.sh`)

Use `tests/run_tests.sh` from the `verus-boogie` root:

```bash
./tests/run_tests.sh [stage options] [target_path]
```

### Repository layout

By default, the script expects these three repos as siblings:

```text
<workspace>/
  verus/
  verus-boogie/
  Strata/
```

So from `verus-boogie`, it uses:
- Verus repo at `../verus` (binary at `../verus/source/target-verus/release/verus`)
- Strata repo at `../Strata`

If your repos are not in this layout, you can override paths with env vars:

```bash
VERUS_DIR=/path/to/verus STRATA_DIR=/path/to/Strata ./tests/run_tests.sh --all /path/to/file.rs
```

You can also override direct binaries if needed:

```bash
VERUS_BIN=/path/to/verus VERUS_LEAN=/path/to/verus-lean ./tests/run_tests.sh --boole /path/to/file.json
```

Boole output directory can be overridden:

```bash
BOOLE_DIR=/path/to/boole-output ./tests/run_tests.sh --boole /path/to/file.rs
```

Stage options:
- `--verus`: export Verus `.rs` to JSON
- `--boole`: generate Boole `.boole.st` plus a Lean verifier wrapper from target
  (`.rs -> JSON -> Boole`, `.json -> Boole`)
- `--verify`: run Strata Boole verification on generated Lean wrappers
- `--all`: run `--verus --boole --verify`

Other options:
- `--solver <name>` (default: `cvc5`)
- `--solver-timeout <sec>`
- `--out <path>` output file path for single-target runs
  (supported for single-target `--boole` runs)
- `--verbose`

`target_path` is optional. If provided, it should be a file path:
- `.rs` for Verus export and downstream Boole generation/verification
- `.json` for Boole generation
- `.lean` for Boole verification wrappers

`--boole` is end-to-end by target type:
- `.rs`: runs Verus export + Boole generation
- `.json`: runs Boole generation
- no target: generates Boole files from existing JSON bundles

`target_path` may be relative or absolute.

### Verus -> Boole

```bash
# End-to-end from Verus source to Boole output
./tests/run_tests.sh --boole tests/VerusFiles/FindMax.rs

# From existing JSON to Boole output
./tests/run_tests.sh --boole tests/JSONFilesBoogie/vlir-tests/FindMax/FindMax.json

# Write Boole output to a custom file path
./tests/run_tests.sh --boole tests/VerusFiles/FindMax.rs --out /tmp/FindMax.boole.st
```


Default Boole output directory:
- Boole source files: `tests/BooleFiles`
- Lean verifier wrappers: `tests/BoolePrograms`

### Boole translation internals

The Boole path lowers VLIR directly to `BooleDDM`:

- `VerusLean/VLIR/Boole/Context.lean` tracks fvar/bvar scope state and typed
  support-declaration needs.
- `Names.lean`, `Coercions.lean`, `Signatures.lean`, and `Prelude.lean` hold
  name normalization, numeric coercion policy, known helper signatures, and
  text-prelude planning metadata.
- `Normalize.lean` performs pure VLIR rewrites before BooleDDM construction:
  temp inlining, compute-proof recovery, decrease stripping, return-artifact
  stripping, and capture-avoiding substitution.
- `ForLoop.lean` recognizes Verus iterator scaffolding and returns a recovered
  source-style loop plan; `Translate.lean` emits that plan as BooleDDM.
- `Emit.lean` parses selected text preludes, merges operations, and renders via
  Strata's Boole formatter.

`docs/seq-vec-pipeline.md` documents the live Seq/Vec support path.
`docs/boole-translation-todo.md` tracks remaining cleanup work.


## Contributors

- Cayden Codel, PhD student at Carnegie Mellon University (ccodel@andrew.cmu.edu)
- James Gallicchio, PhD student at Carnegie Mellon University (jgallicc@andrew.cmu.edu)
