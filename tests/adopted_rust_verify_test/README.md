# adopted_rust_verify_test

This directory holds local Verus shards adopted from
`verus/source/rust_verify_test/tests/`.

These files are:
- hand-extracted from the upstream harness-style `rust_verify_test` sources
- simplified into standalone `.rs` inputs that `verus-boogie` can run directly
- treated as part of the local `vlir-tests` suite by `tests/run_tests.sh` and
  `tests/regress_examples.sh`

Current policy:
- keep the adopted file name aligned with the upstream source shard when practical
- preserve existing output basenames (for example `maps`, `seqs`, `sets`)
- add a provenance comment at the top of each adopted file
- only adopt curated shards that make sense as standalone translator tests;
  do not blindly mirror the full `rust_verify_test` harness tree
