import Lake
open Lake DSL

package «ttfpi» where
  -- add package configuration options here

lean_lib «TTFPI» where
  -- add library configuration options here

require batteries from git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_exe «ttfpi» where
  root := `Main
