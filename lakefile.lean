import Lake
open Lake DSL

package «verus-lean» where
  -- add package configuration options here

lean_lib «VerusLean» where
  -- add library configuration options here

@[default_target]
lean_exe «verus-lean» where
  root := `Main
