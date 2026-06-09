import Lake
open Lake DSL

package «verus-lean» where
  -- enable experimental `module` syntax for dependencies on Lean 4.26
  leanOptions := #[
    ⟨`experimental.module, true⟩
  ]

lean_lib «VerusLean» where
  -- add library configuration options here

@[default_target]
lean_exe «verus-lean» where
  root := `Main

lean_exe VerusParser where
  root := `VerusLean.VLIRParser

require Strata from "../Strata"
require StrataBoole from "../Strata/StrataBoole"
