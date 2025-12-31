import Lake
open Lake DSL

package «leverage» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «Leverage» where
  globs := #[.submodules `Leverage]
  srcDir := "."
