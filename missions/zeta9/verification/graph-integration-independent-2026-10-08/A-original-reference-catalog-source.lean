import Theorems.Thm_ZetaNine_AnalyticUniformMomentBound_actualMoment_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_changing_quartics_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
import GAIExprDag
import Lean
open Lean Meta Elab Command
set_option autoImplicit false
set_option maxRecDepth 200000
run_cmd liftTermElabM do
  let ci ← getConstInfo ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type ci.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  unless Expr.equal ci.type a && Expr.equal ci.type b && (← isDefEq ci.type a) do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound"),("type_raw",toJson (reprStr ci.type)),("complete_type_roundtrip",toJson true)]).compress)
  let ci ← getConstInfo ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type ci.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  unless Expr.equal ci.type a && Expr.equal ci.type b && (← isDefEq ci.type a) do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound"),("type_raw",toJson (reprStr ci.type)),("complete_type_roundtrip",toJson true)]).compress)
  let ci ← getConstInfo ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type ci.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  unless Expr.equal ci.type a && Expr.equal ci.type b && (← isDefEq ci.type a) do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one"),("type_raw",toJson (reprStr ci.type)),("complete_type_roundtrip",toJson true)]).compress)
