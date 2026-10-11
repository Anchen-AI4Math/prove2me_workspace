import Lean
open Lean
run_meta do
  let envPath ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (envPath.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
  let search ← searchPathRef.get
  for name in [`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet, `missions.zeta9.formalization.CoefficientMapInjectivity, `missions.zeta9.formalization.CoefficientMapPartialFractions, `missions.zeta9.formalization.CoefficientMapReflection, `missions.zeta9.formalization.CoefficientMapFiniteSum, `missions.zeta9.formalization.CoefficientMapSummation, `missions.zeta9.formalization.CoefficientMapAggregate, `missions.zeta9.formalization.CoefficientMapTelescoper, `missions.zeta9.formalization.CoefficientMapShiftDegree, `missions.zeta9.formalization.CoefficientMapKernelBridge, `Definitions.Def_ZetaNine_HarmonicStability, `NativeKernelAuthorControl, `NativeKernelIndependentControl, `NativeValueComparisonDefinition, `NativeKernelValueComparisonDefinition, `NativeRootNodeValueComparison] do
    let path ← findOLean name
    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str name.toString),("resolved_olean",Json.str path.toString)]).compress
