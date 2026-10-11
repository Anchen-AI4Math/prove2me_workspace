import Lean
open Lean
def main : IO Unit := do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println ((Json.mkObj [("kind", Json.str "actual_search_path"), ("LEAN_PATH", Json.str (path.getD ""))]).compress)
  for m in (["Definitions.Def_ZetaNine_CoefficientMap", "Definitions.Def_ZetaNine_CoefficientMapJet", "Definitions.Def_ZetaNine_CoefficientMapInjectivity", "Definitions.Def_ZetaNine_CoefficientMapPartialFractions", "Definitions.Def_ZetaNine_CoefficientMapReflection", "Definitions.Def_ZetaNine_CoefficientMapFiniteSum", "Definitions.Def_ZetaNine_CoefficientMapSummation", "Definitions.Def_ZetaNine_CoefficientMapAggregate", "Definitions.Def_ZetaNine_HarmonicStability", "Definitions.Def_ZetaNine_CoefficientMapTelescoper", "Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_weightedR_is_difference", "Theorems.Thm_ZetaNine_CoefficientMapTelescoper_actual_weightedR_is_difference", "Solutions.Sol_ZetaNine_CoefficientMapTelescoper_telescoper_actual_rational_representation", "Theorems.Thm_ZetaNine_CoefficientMapTelescoper_telescoper_actual_rational_representation", "Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound", "Theorems.Thm_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound", "StagedValueComparisonDefinition"] : List String) do
    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println ((Json.mkObj [("kind", Json.str "actual_module_resolution"), ("module", Json.str m), ("resolved_olean", Json.str p.toString)]).compress)
