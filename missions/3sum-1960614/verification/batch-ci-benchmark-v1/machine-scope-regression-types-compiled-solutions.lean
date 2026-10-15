import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Bands_tripleOwner_injective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_three_relation
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_sum_incidenceCount_sq
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Histograms_selected_pairMass_bound
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_jointPair_card_le_cube
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_four_relation_of_mask_ne
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_oneHot_four_independent
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_raw_second_moment
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_raw_second_moment_five
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_trimmed_second_moment

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
  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-scope-regression-inverse-names.json"
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

  let raw ← IO.FS.readFile "missions/3sum-1960614/verification/machine-scope-regression-compiled-solution-inputs.json"
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
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-scope-regression-types-compiled-solutions.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} compiled solution CI types; retained {retainedRegions.size} regions"
