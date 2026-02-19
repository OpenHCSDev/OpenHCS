import Lake
open Lake DSL

package «ssot» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "a6276f4c6097675b1cf5ebd49b1146b735f38c02"

@[default_target]
lean_lib «Ssot» where
  globs := #[.submodules `Ssot]
  srcDir := "."
