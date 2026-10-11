import Lean
open Lean
#eval do
  IO.println ((Json.mkObj [("kind", Json.str "actual_search_path"), ("LEAN_PATH", Json.str ((← IO.getEnv "LEAN_PATH").getD ""))]).compress)
  for m in (["missions.zeta9.formalization.CoefficientMap", "missions.zeta9.formalization.CoefficientMapJet", "missions.zeta9.formalization.CoefficientMapInjectivity", "missions.zeta9.formalization.CoefficientMapPartialFractions", "missions.zeta9.formalization.CoefficientMapReflection", "missions.zeta9.formalization.CoefficientMapFiniteSum", "missions.zeta9.formalization.CoefficientMapSummation", "missions.zeta9.formalization.CoefficientMapAggregate", "missions.zeta9.formalization.CoefficientMapTelescoper", "Definitions.Def_ZetaNine_HarmonicStability", "NativeTelescoperAuthorControl", "NativeTelescoperIndependentControl", "NativeValueComparisonDefinition"] : List String) do
    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println ((Json.mkObj [("kind", Json.str "actual_module_resolution"), ("module", Json.str m), ("resolved_olean", Json.str p.toString)]).compress)
