import Submission.ThreeSum.Bands
import Submission.ThreeSum.Coloring
import Submission.ThreeSum.HashFamily
import Submission.ThreeSum.Histograms

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
  pure ()
  let selected : Array (String × Name) := #[("ThreeSum.Bands.tripleOwner_injective", `ThreeSum.Bands.tripleOwner_injective), ("ThreeSum.Coloring.two_coordinates_separate", `ThreeSum.Coloring.two_coordinates_separate), ("ThreeSum.HashFamily.three_relation", `ThreeSum.HashFamily.three_relation), ("ThreeSum.HashFamily.sum_incidenceCount_sq", `ThreeSum.HashFamily.sum_incidenceCount_sq), ("ThreeSum.HashFamily.hashMap_surjective", `ThreeSum.HashFamily.hashMap_surjective), ("ThreeSum.HashFamily.linear_fiber_card", `ThreeSum.HashFamily.linear_fiber_card), ("ThreeSum.Histograms.selected_pairMass_bound", `ThreeSum.Histograms.selected_pairMass_bound), ("ThreeSum.Coloring.reduction_correct", `ThreeSum.Coloring.reduction_correct), ("ThreeSum.HashFamily.jointPair_card_le_cube", `ThreeSum.HashFamily.jointPair_card_le_cube), ("ThreeSum.HashFamily.four_relation_of_mask_ne", `ThreeSum.HashFamily.four_relation_of_mask_ne), ("ThreeSum.HashFamily.oneHot_four_independent", `ThreeSum.HashFamily.oneHot_four_independent), ("ThreeSum.HashFamily.raw_second_moment", `ThreeSum.HashFamily.raw_second_moment), ("ThreeSum.HashFamily.raw_second_moment_five", `ThreeSum.HashFamily.raw_second_moment_five), ("ThreeSum.HashFamily.trimmed_second_moment", `ThreeSum.HashFamily.trimmed_second_moment)]
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
  IO.FS.writeFile "missions/3sum-1960614/verification/machine-scope-regression-types-native.json" (Json.arr records).pretty
  logInfo s!"recorded {records.size} exact declaration types"
