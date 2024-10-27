import Lake
open Lake DSL

package «HigherRankedSyntax» where
  -- add package configuration options here

lean_lib «HigherRankedSyntax» where
  -- add library configuration options here

@[default_target]
lean_exe «higherrankedsyntax» where
  root := `Main
