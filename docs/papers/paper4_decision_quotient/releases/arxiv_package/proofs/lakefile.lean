import Lake
open Lake DSL

package «decision_quotient» where
  -- No custom Lean options needed for build

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.16.0"

@[default_target]
lean_lib «DecisionQuotient» where
  globs := #[.submodules `DecisionQuotient]
  srcDir := "."
