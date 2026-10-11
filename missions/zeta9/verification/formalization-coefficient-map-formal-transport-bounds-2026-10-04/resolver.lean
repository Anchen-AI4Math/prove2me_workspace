import Lean
open Lean
def main : IO Unit := do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println ((Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress)
  for m in (["missions.zeta9.formalization.CoefficientMap", "missions.zeta9.formalization.CoefficientMapJet", "missions.zeta9.formalization.CoefficientMapInjectivity", "missions.zeta9.formalization.CoefficientMapPartialFractions", "missions.zeta9.formalization.CoefficientMapReflection", "missions.zeta9.formalization.CoefficientMapFiniteSum", "missions.zeta9.formalization.CoefficientMapSummation", "missions.zeta9.formalization.CoefficientMapAggregate", "missions.zeta9.formalization.CoefficientMapTelescoper", "missions.zeta9.formalization.CoefficientMapShiftDegree", "missions.zeta9.formalization.CoefficientMapKernelBridge", "missions.zeta9.formalization.CoefficientMapConnection", "missions.zeta9.formalization.CoefficientMapParameterShift", "Definitions.Def_ZetaNine_HarmonicStability", "missions.zeta9.formalization.CoefficientMapFormalTransportData", "missions.zeta9.formalization.CoefficientMapFormalTransportBounds"] : List String) do
    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println ((Json.mkObj [("kind",Json.str "actual_module_resolution"),("module",Json.str m),("resolved_olean",Json.str p.toString)]).compress)
