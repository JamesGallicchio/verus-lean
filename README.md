# verus-lean: A Verus-Lean connection

The Lean backend to a [verus fork](https://github.com/ccodel/verus)
that allows for the export of verus definitions and verification conditions to Lean.

This repository now supports two main translation paths:
- `Verus -> Lean`
- `Verus -> Strata Core` (and `StrataVerify`)

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
./lake/build/bin/verus-lean <path/to/serialized_verus.json> [path/to/lean/output.lean]
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
VERUS_BIN=/path/to/verus VERUS_LEAN=/path/to/verus-lean ./tests/run_tests.sh --boogie /path/to/file.json
```

Stage options:
- `--verus`: export Verus `.rs` to JSON
- `--boogie`: translate JSON to Strata Core (`.core.st`)
- `--lean`: translate Lean JSON to Lean output
- `--verify`: run `StrataVerify` on generated Core
- `--all`: run `--verus --boogie --verify`

Other options:
- `--solver <name>` (default: `cvc5`)
- `--solver-timeout <sec>`
- `--verbose`

`target_path` is optional. If provided, it should be a file path:
- `.rs` for Verus export (and downstream boogie/verify if selected)
- `.json` for boogie/lean translation
- `.core.st` for verify

`target_path` may be relative or absolute.

### Verus -> Lean

```bash
# Export + Lean translation for one Verus file
./tests/run_tests.sh --verus --lean tests/VerusFiles/FindMax.rs

# Lean translation from an existing Lean JSON
./tests/run_tests.sh --lean tests/JSONFilesLean/FindMax.json
```

### Verus -> Strata Core / StrataVerify

```bash
# Export + Core translation + Strata verification
./tests/run_tests.sh --all tests/VerusFiles/FindMax.rs

# Translate one exported JSON file
./tests/run_tests.sh --boogie tests/JSONFilesBoogie/vlir-tests/FindMax/FindMax.json

# Verify one generated Core file
./tests/run_tests.sh --verify tests/BoogieFiles/vlir-tests/FindMax.core.st
```


## Contributors

- Cayden Codel, PhD student at Carnegie Mellon University (ccodel@andrew.cmu.edu)
- James Gallicchio, PhD student at Carnegie Mellon University (jgallicc@andrew.cmu.edu)
