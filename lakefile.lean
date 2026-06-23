import Lake
open Lake DSL

package «verus-lean» where
  -- enable experimental `module` syntax for dependencies on Lean 4.26
  leanOptions := #[
    ⟨`experimental.module, true⟩
  ]
  -- Raise the language-server worker thread stack (default ~8 MB). Large
  -- generated Boole programs (e.g. the b1 field-mul benchmark) compile each
  -- `#strata` command to a deeply nested term, and the LCNF compiler's
  -- structural recursion overflows the default stack during elaboration.
  -- `lake serve` forwards these to `lean --server`, which propagates `-s`
  -- (thread stack size in KB) to each file worker.
  moreGlobalServerArgs := #["-s", "32768"]

lean_lib «VerusLean» where
  -- add library configuration options here

@[default_target]
lean_exe «verus-lean» where
  root := `Main

lean_exe VerusParser where
  root := `VerusLean.VLIRParser

require Strata from "../Strata"
require StrataBoole from "../Strata-Boole"
