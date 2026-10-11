import Lake
open Lake DSL
package zeta9TelescoperOfflineAuthor where
  buildDir := "D:/users/self_projects/prove2me_workspace/missions/zeta9/.rt/t1/b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapTelescoper]
  globs := #[.one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity, .one `missions.zeta9.formalization.CoefficientMapPartialFractions, .one `missions.zeta9.formalization.CoefficientMapReflection, .one `missions.zeta9.formalization.CoefficientMapFiniteSum, .one `missions.zeta9.formalization.CoefficientMapSummation, .one `missions.zeta9.formalization.CoefficientMapAggregate, .one `missions.zeta9.formalization.CoefficientMapTelescoper]
lean_lib NativeControls where
  roots := #[`NativeTelescoperAuthorControl, `NativeTelescoperIndependentControl]
  globs := #[.one `NativeTelescoperAuthorControl, .one `NativeTelescoperIndependentControl]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
