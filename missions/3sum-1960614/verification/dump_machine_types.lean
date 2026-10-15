import Submission.ThreeSum.CompleteCostBridge
import Submission.ThreeSum.ModelWitnessBounds

open Lean

set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false

/- Phase 5 reference types from the elaborated environment, not source parsing.
   Run after the memory-intensive standalone build finishes. This does not
   modify the source tree or the official Stage 1 / Stage 2 oracles. -/
run_meta do
  let env ← getEnv
  let modules := env.header.moduleNames
  let mut lines : Array String := #[]
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let some mod := modules[idx.toNat]? | continue
    unless (`Submission).isPrefixOf mod || (`Closed3Sum).isPrefixOf mod do continue
    unless !name.isInternal || (privateToUserName? name).isSome do continue
    let typeText := (← Meta.ppExpr ci.type).pretty
    lines := lines.push <| (Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson mod.toString),
      ("levelParams", toJson (ci.levelParams.map Name.toString)),
      ("printedType", toJson typeText),
      ("rawType", toJson (reprStr ci.type))]).compress
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-original-types.jsonl"
    (String.intercalate "\n" lines.toList ++ "\n")
  logInfo s!"wrote {lines.size} original elaborated types"
