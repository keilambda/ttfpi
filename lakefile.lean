import Lake
open Lake DSL

package «ttfpi» where
  -- add package configuration options here

lean_lib «TTFPI» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.13.0"
require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.13.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"
require calcify from git "https://github.com/nomeata/lean-calcify"

meta if get_config? env = some "dev" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.13.0"
