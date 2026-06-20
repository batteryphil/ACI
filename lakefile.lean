import Lake
open Lake DSL

package my_project where

@[default_target]
lean_lib ACI {
  srcDir := "."
}
