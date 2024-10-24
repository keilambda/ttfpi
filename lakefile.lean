import Lake
open Lake DSL

package «ttfpi» where
  -- add package configuration options here

lean_lib «TTFPI» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.11.0"
require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.11.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.11.0"

@[default_target]
lean_exe «ttfpi» where
  root := `Main
