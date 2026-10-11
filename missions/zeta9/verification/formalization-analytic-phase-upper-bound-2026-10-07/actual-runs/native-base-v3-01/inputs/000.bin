import Lake
open Lake DSL
package zeta9ActualPhaseNativeAuthor where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib ActualPhase where
  roots := #[`missions.zeta9.formalization.AnalyticPhaseUpperBound]
  globs := #[.one `missions.zeta9.formalization.AnalyticPhase, .one `missions.zeta9.formalization.AnalyticPhaseUpperBound]
