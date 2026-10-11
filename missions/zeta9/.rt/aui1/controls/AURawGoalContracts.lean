import AUExprDag
import AnalyticWeightedBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open Lean Meta Elab Command
open ZetaNine.AnalyticFactorialBounds
open ZetaNine.AnalyticMomentBounds
open ZetaNine.AnalyticPSeriesTail
open ZetaNine.AnalyticPhase
open ZetaNine.AnalyticRationalFactorial
open ZetaNine.AnalyticRationalLogBound
open ZetaNine.AnalyticRationalTail
open ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMap

private def afEmit (j : Json) : MetaM Unit := do
  let action : IO Unit := do
    let stdout ← IO.getStdout
    stdout.putStrLn ("AU_RECORD|" ++ j.compress)
    stdout.flush
  liftM action

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some value := ci.value? true | throwError "Missing complete proof/definition value: {n}"
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
  let (rt,rv) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let exactType := Expr.equal ci.type rt
  let exactValue := Expr.equal value rv
  unless exactType && exactValue do throwError "Full-field Expr DAG changed an expression: {n}"
  let typeKernel ← isDefEq ci.type rt
  let valueKernel ← isDefEq value rv
  let typed ← isDefEq (← inferType rv) ci.type
  unless typeKernel && valueKernel && typed do
    throwError "Complete reconstructed proof/value does not have its exact complete type: {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",toJson payload.compress),
    ("value_raw_format",toJson "lossless lean-expr-dag-v1; full type_root and value_root"),
    ("all_fields_type_Expr_equal",toJson exactType),("all_fields_value_Expr_equal",toJson exactValue),
    ("full_type_kernel_equal",toJson typeKernel),("full_value_kernel_equal",toJson valueKernel),
    ("value_type_isDefEq",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]


namespace AUIndependentContract

theorem raw_real_rational_quartic_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, ((CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) *
      W.eval (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) + (n : ℚ))) : ℚ) : ℝ)| ≤
      (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) *
        ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n) *
          (∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)) := by
  simpa only [actualWeightedSequence, CoefficientMap.weightedR, analyticPrefactor,
    weightedCoefficientHeight, momentBoundConstant] using actualWeighted_uniform_bound n hn W hW

theorem raw_real_rational_quartic_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖((CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) *
      W.eval (((m + 1 : ℕ) : ℚ) * (((m + 1 : ℕ) : ℚ) + (n : ℚ))) : ℚ) : ℝ)‖) := by
  simpa only [actualWeightedSequence, CoefficientMap.weightedR] using actualWeighted_norm_summable n hn W hW

theorem raw_five_true_moments_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, (CoefficientMap.actualR n ((m + 1 : ℕ) : ℚ) : ℝ) *
      (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) + (n : ℝ))) ^ r) ≤
      (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) *
        ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  simpa only [actualMoment, actualMomentSequence, actualMomentTerm, momentBoundConstant] using
    actualMoment_uniform_bound n r hn hr

theorem explicit_error_limit : Tendsto
    (fun n : ℕ => (Real.log (5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7) +
      10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)) atTop (𝓝 0) := by
  simpa only [uniformError, momentBoundConstant] using uniformError_tendsto_zero

end AUIndependentContract

run_cmd liftTermElabM do
  afRecord "independent_raw_goal_contract" ``AUIndependentContract.raw_real_rational_quartic_bound
  afRecord "independent_raw_goal_contract" ``AUIndependentContract.raw_real_rational_quartic_norm_summable
  afRecord "independent_raw_goal_contract" ``AUIndependentContract.raw_five_true_moments_bound
  afRecord "independent_raw_goal_contract" ``AUIndependentContract.explicit_error_limit
