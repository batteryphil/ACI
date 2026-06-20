import Lake
open Lake DSL

package "my_project" where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib AciLib where
  globs := #[.andSubmodules `AciLib]
  srcDir := "."
