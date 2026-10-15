import Solutions.Sol_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogLevel_program_meets

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
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-platform-inverse-names.json"
  let json ← match Json.parse raw with
    | .ok value => pure value
    | .error message => throwError message
  let object ← match json.getObj? with
    | .ok value => pure value
    | .error message => throwError message
  for (new,old) in object.toArray do
    let original ← match old.getStr? with
      | .ok value => pure value
      | .error message => throwError message
    names := names.insert new.toName original.toName

  let selected : Array (String × Name) := #[("ThreeSum.LightReportingCatalogLevel.program_meets", `solution)]
  let mut records : Array Json := #[]
  for (label, name) in selected do
    let ci ← getConstInfo name
    let levels := ci.levelParams.zipIdx |>.map fun (_,i) => Level.param (Name.num `universe i)
    let original := ci.type.instantiateLevelParams ci.levelParams levels
    let normalized := normalizeThreeSumUploadType names original
    records := records.push <| Json.mkObj [
      ("name",toJson label),("universeCount",toJson ci.levelParams.length),
      ("rawType",toJson (reprStr ci.type)),
      ("printedType",toJson (← Meta.ppExpr ci.type).pretty),
      ("normalizedType",toJson (reprStr normalized))]
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-platform-types-solution-451.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
