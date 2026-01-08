import Lake
open Lake DSL

package «ssot» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Ssot» where
  globs := #[.submodules `Ssot]
  srcDir := "."

