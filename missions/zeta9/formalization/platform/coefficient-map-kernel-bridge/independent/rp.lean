import Lean
open Lean
run_meta do
  let envPath ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (envPath.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
  let search ← searchPathRef.get
  for name in [`Definitions.Def_ZetaNine_HarmonicStability, `Definitions.Def_ZetaNine_CoefficientMap, `Definitions.Def_ZetaNine_CoefficientMapJet, `Definitions.Def_ZetaNine_CoefficientMapInjectivity, `Definitions.Def_ZetaNine_CoefficientMapPartialFractions, `Definitions.Def_ZetaNine_CoefficientMapReflection, `Definitions.Def_ZetaNine_CoefficientMapFiniteSum, `Definitions.Def_ZetaNine_CoefficientMapSummation, `Definitions.Def_ZetaNine_CoefficientMapAggregate, `Definitions.Def_ZetaNine_CoefficientMapTelescoper, `Definitions.Def_ZetaNine_CoefficientMapShiftDegree, `Definitions.Def_ZetaNine_CoefficientMapKernelBridge, `Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_original_quartic_aggregate_kernel_zero, `Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_original_quartic_aggregate_kernel_zero, `Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_original_five_dimensional_map_bijective, `Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_original_five_dimensional_map_bijective, `Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute, `Theorems.Thm_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute, `StagedValueComparisonDefinition, `StagedKernelValueComparisonDefinition, `StagedRootNodeValueComparison] do
    let path ← findOLean name
    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str name.toString),("resolved_olean",Json.str path.toString)]).compress
