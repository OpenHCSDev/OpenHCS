import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true",
  "-Dpp.proofs.withType=false"
]

def moreLeanArgs := moreServerArgs

def weakLeanArgs : Array String :=
  if get_config? CI |>.isSome then
    #["-DwarningAsError=true"]
  else
    #[]

package «unified_proofs» where
  moreServerArgs := moreServerArgs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-------------------------------------------------
-- Paper 1: Typing Discipline
-------------------------------------------------
@[default_target]
lean_lib «axis_framework» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.axis_framework]

lean_lib «abstract_class_system» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.abstract_class_system]

lean_lib «nominal_resolution» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.nominal_resolution]

lean_lib «context_formalization» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.context_formalization]

lean_lib «discipline_migration» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.discipline_migration]

lean_lib «python_instantiation» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.python_instantiation]

lean_lib «java_instantiation» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.java_instantiation]

lean_lib «typescript_instantiation» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.typescript_instantiation]

lean_lib «rust_instantiation» where
  moreLeanArgs := moreLeanArgs
  weakLeanArgs := weakLeanArgs
  roots := #[`Paper1.rust_instantiation]

