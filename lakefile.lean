import Lake
open Lake DSL

package «ttfp» where
  -- add package configuration options here

lean_lib «Ttfp» where
  -- add library configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_exe «ttfp» where
  root := `Main
