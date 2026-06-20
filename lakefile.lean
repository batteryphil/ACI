import Lake
open Lake DSL

package "my_project" where
  srcDir := "."

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

@[default_target]
lean_lib "MyProject" where
  roots := #[ `ACIManifold, `Governor, `ACI_Governance.Root, `ACI_Governance.Node_2, `ACI_System_Kernel ]
