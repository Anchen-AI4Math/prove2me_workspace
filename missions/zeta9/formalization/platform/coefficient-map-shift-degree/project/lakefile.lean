import Lake
open Lake DSL
package zeta9ShiftDegreeOfflineAuthor
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapShiftDegree]
  globs := #[.one `missions.zeta9.formalization.CoefficientMapShiftDegree]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
