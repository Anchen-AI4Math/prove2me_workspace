import Solutions.Sol_ThreeSum1960614_model_platform_bound

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

run_meta do
  let names : Array (String × Name) := #[("ThreeSum1960614.FixedModel.bound_of_witnesses", `ThreeSum1960614.FixedModel.bound_of_witnesses), ("ThreeSum1960614.FixedModel.witness_logs", `ThreeSum1960614.FixedModel.witness_logs), ("ThreeSum1960614.FixedModel.complete_lower_bound", `solution)]
  let mut records : Array Json := #[]
  for (label, name) in names do
    let ci ← getConstInfo name
    records := records.push <| Json.mkObj [
      ("name", toJson label),
      ("levels", toJson (ci.levelParams.map Name.toString)),
      ("printedType", toJson (← Meta.ppExpr ci.type).pretty),
      ("rawType", toJson (reprStr ci.type))]
  IO.FS.writeFile "missions/3sum-1960614/verification/model-types-platform.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
