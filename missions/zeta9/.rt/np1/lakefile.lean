import Lake
open Lake DSL
package zeta9ParameterShiftNative where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapParameterShift]
  globs := #[.submodules `missions.zeta9.formalization]
lean_lib Definitions
