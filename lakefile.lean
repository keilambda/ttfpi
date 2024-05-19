import Lake
open Lake DSL

package «ttfp» where
  -- add package configuration options here

lean_lib «Ttfp» where
  -- add library configuration options here

@[default_target]
lean_exe «ttfp» where
  root := `Main
