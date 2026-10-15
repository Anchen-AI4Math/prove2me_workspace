import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Bands_tripleOwner_injective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Coloring_two_coordinates_separate
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_three_relation
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_sum_incidenceCount_sq
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_hashMap_surjective
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_linear_fiber_card
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Histograms_selected_pairMass_bound
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Coloring_reduction_correct
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

  let selected : Array (String × Name) := #[("ThreeSum.Bands.tripleOwner_injective", `ThreeSum1960614.MachineScopeRegression.ThreeSum.Bands.tripleOwner_injective), ("ThreeSum.Coloring.two_coordinates_separate", `ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.two_coordinates_separate), ("ThreeSum.HashFamily.three_relation", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation), ("ThreeSum.HashFamily.sum_incidenceCount_sq", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.sum_incidenceCount_sq), ("ThreeSum.HashFamily.hashMap_surjective", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.hashMap_surjective), ("ThreeSum.HashFamily.linear_fiber_card", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.linear_fiber_card), ("ThreeSum.Histograms.selected_pairMass_bound", `ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.selected_pairMass_bound), ("ThreeSum.Coloring.reduction_correct", `ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.reduction_correct), ("ThreeSum.HashFamily.jointPair_card_le_cube", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.jointPair_card_le_cube), ("ThreeSum.HashFamily.four_relation_of_mask_ne", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.four_relation_of_mask_ne), ("ThreeSum.HashFamily.oneHot_four_independent", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot_four_independent), ("ThreeSum.HashFamily.raw_second_moment", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.raw_second_moment), ("ThreeSum.HashFamily.raw_second_moment_five", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.raw_second_moment_five), ("ThreeSum.HashFamily.trimmed_second_moment", `ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.trimmed_second_moment)]
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
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-scope-regression-types-stubs.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
