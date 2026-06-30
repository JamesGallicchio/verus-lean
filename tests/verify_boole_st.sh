#!/usr/bin/env bash
# Verify a standalone Boole program (`.boole.st`) directly — no `.rs` or JSON
# needed. Wraps the program in the `#strata` macro + `Strata.Boole.verify` and
# runs it through `lake env lean` from the StrataBoole package.
#
# Usage:
#   tests/verify_boole_st.sh <program.boole.st> [solver]
#
# `solver` defaults to z3. The StrataBoole lake package is taken from
# $STRATA_BOOLE_DIR, defaulting to the sibling `Strata-Boole` checkout (where the
# dalek seeds live and where the benchmark figures were produced).
#
# Example:
#   tests/verify_boole_st.sh /tmp/b2.boole.st z3
set -uo pipefail

st="${1:?usage: verify_boole_st.sh <program.boole.st> [solver]}"
solver="${2:-z3}"

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
pkg="${STRATA_BOOLE_DIR:-$ROOT_DIR/../Strata-Boole}"

if [ ! -f "$st" ]; then echo "no such program: $st" >&2; exit 2; fi
if [ ! -e "$pkg/lakefile.lean" ] && [ ! -e "$pkg/lakefile.toml" ]; then
  echo "no lake package at $pkg (set STRATA_BOOLE_DIR)" >&2; exit 2
fi

wrap="$(mktemp "${TMPDIR:-/tmp}/boole_wrap.XXXXXX.lean")"
{
  echo "import StrataBoole.MetaVerifier"
  echo "open Strata"
  echo "set_option maxRecDepth 100000"
  echo "private def prog : StrataDDM.Program :="
  echo "#strata"
  cat "$st"            # the .boole.st already begins with `program Boole;`
  echo "#end"
  echo "#eval Strata.Boole.verify \"$solver\" prog (options := .quiet)"
} > "$wrap"

# `-s 131072` gives Lean a 128 MB stack (KB units): the heaviest programs (b1/b4)
# overflow the ~8 MB default while the LCNF compiler builds the #strata data-defn.
( cd "$pkg" && lake env lean -s 131072 "$wrap" )
rc=$?
rm -f "$wrap"
exit "$rc"
