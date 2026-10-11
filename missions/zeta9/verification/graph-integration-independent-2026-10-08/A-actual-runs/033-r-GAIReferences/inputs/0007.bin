import Theorems.Thm_ZetaNine_AnalyticUniformMomentBound_actualMoment_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_changing_quartics_uniform_bound
import Theorems.Thm_ZetaNine_AnalyticWeightedBound_actual_weighted_uniform_o_one
import GAIExprDag
import Lean
open Lean Meta Elab Command
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 16000000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
theorem reference_moment (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤ ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r)  := by
  apply ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
  all_goals assumption

theorem reference_changing (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n (W n) m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n (W n)  := by
  apply ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
  all_goals assumption

theorem reference_uniform :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W  := by
  apply ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
  all_goals assumption

run_cmd liftTermElabM do
  let ci ← getConstInfo ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
  let expected ← getConstInfo ``reference_moment
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type expected.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let rawEqual := Expr.equal ci.type expected.type
  let defEqual ← isDefEq ci.type expected.type
  unless Expr.equal ci.type a && Expr.equal expected.type b && defEqual do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound"),
    ("type_raw",toJson (reprStr ci.type)),("expected_type_raw",toJson (reprStr expected.type)),("type_Expr_equal",toJson rawEqual),
    ("type_isDefEq",toJson defEqual),("complete_type_roundtrip",toJson true),("catalog_value_not_mathematical_proof",toJson true)]).compress)
  let ci ← getConstInfo ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
  let expected ← getConstInfo ``reference_changing
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type expected.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let rawEqual := Expr.equal ci.type expected.type
  let defEqual ← isDefEq ci.type expected.type
  unless Expr.equal ci.type a && Expr.equal expected.type b && defEqual do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound"),
    ("type_raw",toJson (reprStr ci.type)),("expected_type_raw",toJson (reprStr expected.type)),("type_Expr_equal",toJson rawEqual),
    ("type_isDefEq",toJson defEqual),("complete_type_roundtrip",toJson true),("catalog_value_not_mathematical_proof",toJson true)]).compress)
  let ci ← getConstInfo ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
  let expected ← getConstInfo ``reference_uniform
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type expected.type)
  let (a,b) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let rawEqual := Expr.equal ci.type expected.type
  let defEqual ← isDefEq ci.type expected.type
  unless Expr.equal ci.type a && Expr.equal expected.type b && defEqual do throwError "Reference full type mismatch"
  liftM <| IO.println ("GAI_RECORD|" ++ (Json.mkObj [("kind",toJson "reference_type_catalog_only"),("name",toJson "ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one"),
    ("type_raw",toJson (reprStr ci.type)),("expected_type_raw",toJson (reprStr expected.type)),("type_Expr_equal",toJson rawEqual),
    ("type_isDefEq",toJson defEqual),("complete_type_roundtrip",toJson true),("catalog_value_not_mathematical_proof",toJson true)]).compress)
