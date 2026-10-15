import Submission.ThreeSum.CompleteCostBridge
import Submission.ThreeSum.ModelWitnessBounds
import Submission.ThreeSum.FinalSolver

open Lean

run_meta do
  let env ← getEnv
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/extended-reuse-input-names.json"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut recognized : Array String := #[]
  for item in items do
    let text ← match item.getStr? with
      | .ok value => pure value
      | .error message => throwError message
    if Meta.isMatcherCore env text.toName then recognized := recognized.push text
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-native-matchers.json" (toJson recognized).compress
  logInfo s!"recognized {recognized.size} compiler matchers using Lean's own metadata"
