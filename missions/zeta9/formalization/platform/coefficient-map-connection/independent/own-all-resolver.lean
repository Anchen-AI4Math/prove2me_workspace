import Lean
open Lean
run_meta do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress
  for m in [`missions.zeta9.formalization.CoefficientMapConnection,`Definitions.Def_ZetaNine_CoefficientMapConnection,`Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_homogeneous_kernel_zero,`Theorems.Thm_ZetaNine_CoefficientMapConnection_connection_homogeneous_kernel_zero,`Solutions.Sol_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective,`Theorems.Thm_ZetaNine_CoefficientMapConnection_connectionLinearMap_bijective,`Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_five_systems_unique,`Theorems.Thm_ZetaNine_CoefficientMapConnection_connection_five_systems_unique,`NativeValueComparisonDefinition,`StagedValueComparisonDefinition] do
    let p ← findOLean m
    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m.toString),("olean",Json.str p.toString)]).compress
