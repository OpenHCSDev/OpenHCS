import Lake
open Lake DSL

package «TheoreticalMinimality» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «TheoreticalMinimality» where
  globs := #[.submodules `TheoreticalMinimality]

-- Papers 1-3 proofs copied for self-contained archive
lean_lib «Paper1Proofs» where
  globs := #[.submodules `Paper1Proofs]

lean_lib «Paper2Proofs» where
  globs := #[.submodules `Paper2Proofs]

lean_lib «Paper3Proofs» where
  globs := #[.submodules `Paper3Proofs]

