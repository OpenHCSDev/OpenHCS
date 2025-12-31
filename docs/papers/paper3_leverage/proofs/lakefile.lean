import Lake
open Lake DSL

package «leverage» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

@[default_target]
lean_lib «Leverage» where
  globs := #[.submodules `Leverage]
  srcDir := "."
