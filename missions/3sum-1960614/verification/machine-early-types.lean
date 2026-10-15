import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

open Lean
set_option pp.fullNames true
set_option pp.universes true
set_option pp.explicit true
set_option pp.notation false
set_option maxRecDepth 10000

private partial def normalizeThreeSumUploadType (names : Std.HashMap Name Name) (expr : Expr) : Expr :=
  match expr with
  | .const name levels => .const ((names.get? name).getD name) levels
  | .app f a => .app (normalizeThreeSumUploadType names f) (normalizeThreeSumUploadType names a)
  | .lam _ type body info => .lam .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .forallE _ type body info => .forallE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names body) info
  | .letE _ type value body nondep => .letE .anonymous (normalizeThreeSumUploadType names type) (normalizeThreeSumUploadType names value) (normalizeThreeSumUploadType names body) nondep
  | .mdata _ value => normalizeThreeSumUploadType names value
  | .proj name index value => .proj ((names.get? name).getD name) index (normalizeThreeSumUploadType names value)
  | other => other

run_meta do
  let mut names : Std.HashMap Name Name := {}
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-early-inverse-names.json"
  let object ← ofExcept (Json.parse raw >>= Json.getObj?)
  for (new,old) in object.toArray do
    let original ← ofExcept old.getStr?
    names := names.insert new.toName original.toName

  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-early-type-inputs.json"
  let items ← match Json.parse raw >>= Json.getArr? with
    | .ok value => pure value
    | .error message => throwError message
  let mut records : Array Json := #[]
  let mut retainedRegions : Array CompactedRegion := #[]
  for item in items do
    let label ← match item.getObjValAs? String "name" with
      | .ok value => pure value
      | .error message => throwError message
    let path ← match item.getObjValAs? String "path" with
      | .ok value => pure value
      | .error message => throwError message
    let (data,region) ← readModuleData path
    retainedRegions := retainedRegions.push region
    let candidates := data.constants.filter (fun ci => ci.name == `solution)
    unless candidates.size == 1 do
      throwError "Expected exactly one root solution CI in {path}; got {candidates.size}"
    let ci := candidates[0]!
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let original := ci.type.instantiateLevelParams ci.levelParams levels
    let normalized := normalizeThreeSumUploadType names original
    records := records.push <| Json.mkObj [
      ("name",toJson label),("universeCount",toJson ci.levelParams.length),
      ("rawType",toJson (reprStr ci.type)),
      ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
      ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-early-solution-types.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} compiled solution CI types; retained {retainedRegions.size} regions"

run_meta do
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-early-inverse-names.json"
  let object ← ofExcept (Json.parse raw >>= Json.getObj?)
  let mut names : Std.HashMap Name Name := {}
  for (new,old) in object.toArray do
    let original ← ofExcept old.getStr?
    names := names.insert new.toName original.toName
  let mut records := #[]
  for (label,name) in #[("Light.Ends.while", `ThreeSum1960614.Machine.Light.Ends.while), ("Light.Ends.of_blockSafe", `ThreeSum1960614.Machine.Light.Ends.of_blockSafe), ("Light.Ends.for", `ThreeSum1960614.Machine.Light.Ends.for)] do
    let ci ← getConstInfo name
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let normalized := normalizeThreeSumUploadType names (ci.type.instantiateLevelParams ci.levelParams levels)
    records := records.push <| Json.mkObj [("name",toJson label),
      ("universeCount",toJson ci.levelParams.length),("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-early-stub-types.json" (Json.arr records).pretty
