import Lean
open Lean
run_meta do
  let ep ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (ep.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_HarmonicStability
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_HarmonicStability"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMap
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMap"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapJet
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapJet"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapInjectivity
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapInjectivity"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapPartialFractions
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapPartialFractions"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapReflection
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapReflection"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapFiniteSum
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapFiniteSum"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapSummation
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapSummation"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapAggregate
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapAggregate"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapTelescoper
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapTelescoper"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapShiftDegree
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapShiftDegree"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapKernelBridge
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapKernelBridge"),("object",Json.str p.toString)]).compress
  let p ← findOLean `missions.zeta9.formalization.CoefficientMapMatrix
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "missions.zeta9.formalization.CoefficientMapMatrix"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMap
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMap"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapJet
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapJet"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapInjectivity
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapInjectivity"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapPartialFractions
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapPartialFractions"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapReflection
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapReflection"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapFiniteSum
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapFiniteSum"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapSummation
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapSummation"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapAggregate
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapAggregate"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapTelescoper
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapTelescoper"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapShiftDegree
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapShiftDegree"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapKernelBridge
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapKernelBridge"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Definitions.Def_ZetaNine_CoefficientMapMatrix
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Definitions.Def_ZetaNine_CoefficientMapMatrix"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Solutions.Sol_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Solutions.Sol_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Theorems.Thm_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Theorems.Thm_ZetaNine_CoefficientMapMatrix_actualFMatrix_det_ne_zero"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_coordinates_product"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Solutions.Sol_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute"),("object",Json.str p.toString)]).compress
  let p ← findOLean `Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "Theorems.Thm_ZetaNine_CoefficientMapMatrix_selectedIntegerMultiplier_actual_HasSum_and_absolute"),("object",Json.str p.toString)]).compress
  let p ← findOLean `NativeMatrixAuthorSourceControl
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "NativeMatrixAuthorSourceControl"),("object",Json.str p.toString)]).compress
  let p ← findOLean `NativeMatrixAuthorEndpointControl
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "NativeMatrixAuthorEndpointControl"),("object",Json.str p.toString)]).compress
  let p ← findOLean `NativeMatrixIndependentSourceControl
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "NativeMatrixIndependentSourceControl"),("object",Json.str p.toString)]).compress
  let p ← findOLean `NativeMatrixIndependentBoundaryControl
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "NativeMatrixIndependentBoundaryControl"),("object",Json.str p.toString)]).compress
  let p ← findOLean `NativeValueComparisonDefinition
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "NativeValueComparisonDefinition"),("object",Json.str p.toString)]).compress
  let p ← findOLean `StagedValueComparisonDefinition
  IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str "StagedValueComparisonDefinition"),("object",Json.str p.toString)]).compress
