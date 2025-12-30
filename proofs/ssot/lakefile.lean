import Lake
open Lake DSL

package «ssot» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «Ssot» where
  globs := #[.submodules `Ssot]
  srcDir := "."

