import Submission.ThreeSum.CompleteCostBridge
import Lean
open Lean
run_meta do
  let mut result := #[]
  for name in #[`Light.Ends.for._auto_1, `Light.Ends.for._auto_3] do
    let ci ← getConstInfo name
    result := result.push <| Json.mkObj [("name",toJson name.toString),
      ("type",toJson (reprStr ci.type)),("value",toJson (reprStr ci.value?)),
      ("kind",toJson (match ci with | .defnInfo _ => "definition" | _ => "other"))]
  IO.FS.writeFile "missions/3sum-1960614/verification/probe-native-auto-companions.json" (Json.arr result).pretty
