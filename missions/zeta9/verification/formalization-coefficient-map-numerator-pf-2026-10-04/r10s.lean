import Lean
open Lean
run_meta do
  let ep ← IO.getEnv "LEAN_PATH"
  IO.println (Json.mkObj [("kind",Json.str "actual_environment"),("LEAN_PATH",Json.str (ep.getD "")),("Lean_version",Json.str Lean.versionString)]).compress
  for n in [`missions.zeta9.formalization.CoefficientMap, `missions.zeta9.formalization.CoefficientMapJet, `missions.zeta9.formalization.CoefficientMapInjectivity, `missions.zeta9.formalization.CoefficientMapPartialFractions, `missions.zeta9.formalization.CoefficientMapReflection, `missions.zeta9.formalization.CoefficientMapFiniteSum, `missions.zeta9.formalization.CoefficientMapSummation, `missions.zeta9.formalization.CoefficientMapAggregate, `missions.zeta9.formalization.CoefficientMapTelescoper, `missions.zeta9.formalization.CoefficientMapShiftDegree, `missions.zeta9.formalization.CoefficientMapKernelBridge, `missions.zeta9.formalization.CoefficientMapConnection, `missions.zeta9.formalization.CoefficientMapParameterShift, `Definitions.Def_ZetaNine_HarmonicStability, `missions.zeta9.formalization.CoefficientMapFormalTransportData, `missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions, `ValueAliases] do
    let p ← findOLean n
    IO.println (Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str n.toString),("object",Json.str p.toString)]).compress
