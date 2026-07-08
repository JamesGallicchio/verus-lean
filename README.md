# verus-lean: A Verus-Lean connection

The Lean backend to a [verus fork](https://github.com/ccodel/verus/tree/boogie)
that allows for the export of verus definitions and verification conditions to Lean.

This repository now supports two main translation paths:
- `Verus -> Lean`
- `Verus -> Boole` (direct VLIR -> BooleDDM)

## Building

All building/compiling is done at the root level of the project,
unless otherwise indicated.

`verus-lean` depends on two sibling checkouts, referenced by relative path in
`lakefile.lean`:
- `../Strata-Boole` — the Boole dialect and verifier
- `../Strata` — the Core/DDM backend. `Strata-Boole` builds on it, and
  `verus-lean` also imports a few `Strata` / `StrataDDM` modules directly, so it
  is required here in its own right (not only transitively).

Place both next to `verus-boogie` (see [Repository layout](#repository-layout)),
then build from the `verus-boogie` root:
```
lake build
```
That single command builds the whole graph: Lake compiles `Strata` and
`Strata-Boole` first, in dependency order, then `verus-lean`. You do **not**
need to build the siblings separately beforehand. (They are local *path*
dependencies — nothing is downloaded, and each one's build artifacts land in
its own `.lake/`.)

The compiled binary can be found at `.lake/build/bin/verus-lean`.

(I find it helpful to symlink the `bin/` folder at root level: `ln -s .lake/build/bin bin`,
or perhaps even better, `ln -s .lake/build/bin/verus-lean verus-lean`.)

## Running

You can run the compiled `verus-lean` binary directly:
```
.lake/build/bin/verus-lean boole <path/to/serialized_verus.json> [path/to/output.boole.st]
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

By default, the script expects these repos as siblings:

```text
<workspace>/
  verus/
  verus-boogie/
  Strata/
  Strata-Boole/
```

So from `verus-boogie`, it uses:
- Verus repo at `../verus` — the export front end; the binary at
  `../verus/source/target-verus/release/verus` must be built from the `boogie`
  branch, which carries the Lean JSON export and the `-V new-mut-ref` mode the
  `--verus`/`--all` stages rely on
- Strata repo at `../Strata` — the Core/DDM backend
- Strata-Boole repo at `../Strata-Boole` — the Boole dialect and verifier; the
  `--verify` stage runs `lake env lean` here, and the build links against it

If your repos are not in this layout, you can override paths with env vars:

```bash
VERUS_DIR=/path/to/verus STRATA_DIR=/path/to/Strata STRATA_BOOLE_DIR=/path/to/Strata-Boole ./tests/run_tests.sh --all /path/to/file.rs
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
- `--out <path>` output file path for single-target runs
  (supported for single-target `--boole` runs)
- `--verbose`
- `--synth-disable <names>` disables selected synthesized verification aids
  during Boole generation

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
