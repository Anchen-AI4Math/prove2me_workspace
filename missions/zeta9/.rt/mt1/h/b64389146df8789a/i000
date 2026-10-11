import Lake
open Lake DSL
package zeta9MatrixPlatformIndependent where
  buildDir := "b"
require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "0df444a360eaa60ab8c11dca51a86af692955474"
lean_lib Native where
  roots := #[`missions.zeta9.formalization.CoefficientMapMatrix]
  globs := #[ .one `missions.zeta9.formalization.CoefficientMap, .one `missions.zeta9.formalization.CoefficientMapJet, .one `missions.zeta9.formalization.CoefficientMapInjectivity, .one `missions.zeta9.formalization.CoefficientMapPartialFractions, .one `missions.zeta9.formalization.CoefficientMapReflection, .one `missions.zeta9.formalization.CoefficientMapFiniteSum, .one `missions.zeta9.formalization.CoefficientMapSummation, .one `missions.zeta9.formalization.CoefficientMapAggregate, .one `missions.zeta9.formalization.CoefficientMapTelescoper, .one `missions.zeta9.formalization.CoefficientMapShiftDegree, .one `missions.zeta9.formalization.CoefficientMapKernelBridge, .one `missions.zeta9.formalization.CoefficientMapMatrix ]
lean_lib Definitions
lean_lib Solutions
lean_lib Theorems
lean_lib Controls where
  roots := #[ `NativeMatrixAuthorSourceControl, `NativeMatrixAuthorEndpointControl, `NativeMatrixIndependentSourceControl, `NativeMatrixIndependentBoundaryControl ]
  globs := #[ .one `NativeMatrixAuthorSourceControl, .one `NativeMatrixAuthorEndpointControl, .one `NativeMatrixIndependentSourceControl, .one `NativeMatrixIndependentBoundaryControl ]
lean_lib Comparison where
  roots := #[`NativeValueComparisonDefinition, `StagedValueComparisonDefinition]
  globs := #[.one `NativeValueComparisonDefinition, .one `StagedValueComparisonDefinition]
