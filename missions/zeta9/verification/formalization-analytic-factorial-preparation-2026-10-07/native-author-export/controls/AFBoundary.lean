import AFExprDag
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
    stdout.putStrLn ("AF_RECORD|" ++ j.compress)
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

namespace AFBoundary
theorem factorial_lower_zero : (0 : ℝ) ≤ Real.log (Nat.factorial 0 : ℝ) := by norm_num
theorem factorial_upper_one : Real.log (Nat.factorial 1 : ℝ) ≤ (0 : ℝ) := by norm_num
theorem actual_n_one_k_one_zero : CoefficientMap.actualR 1 (1 : ℚ) = 0 := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct]
theorem actual_n_one_k_two_positive : (0 : ℝ) < (CoefficientMap.actualR 1 (2 : ℚ) : ℝ) :=
  AnalyticRationalFactorial.actualR_real_pos 1 2 (by norm_num)
theorem raw_n_one_first_term_zero : actualMomentSequence 1 4 0 = 0 :=
  actualMomentTerm_zero_of_pos_le 1 4 1 (by norm_num) (by norm_num)
theorem n_one_r_four_tail_exponent : tailPower 1 4 = 8 := by norm_num [tailPower]
theorem n_one_compact_contains_only_zero :
    (∑ m ∈ range (2 * 1 - 1), actualMomentSequence 1 4 m) = 0 := by
  norm_num [raw_n_one_first_term_zero]
theorem all_indices_nonnegative : ∀ n r m : ℕ, 0 ≤ actualMomentSequence n r m :=
  actualMomentSequence_nonneg
theorem no_even_input_for_actual_bound : ∀ n : ℕ, 1 ≤ n →
    |∑' m : ℕ, actualWeightedSequence n (1 : ℚ[X]) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (1 : ℚ[X]) := by
  intro n hn
  exact actualWeighted_uniform_bound n hn 1 (by norm_num)
theorem zero_polynomial_series : ∀ n m : ℕ, actualWeightedSequence n (0 : ℚ[X]) m = 0 := by
  intro n m
  simp [actualWeightedSequence, CoefficientMap.weightedR]
theorem zero_coefficient_height : ∀ n : ℕ, weightedCoefficientHeight n (0 : ℚ[X]) = 0 := by
  intro n
  simp [weightedCoefficientHeight]
theorem negative_constant_has_domain : (-1 : ℚ[X]).natDegree ≤ 4 := by norm_num
theorem excluded_n_zero : ¬ (1 ≤ (0 : ℕ)) := by norm_num
theorem excluded_degree_five : ¬ (Polynomial.X ^ 5 : ℚ[X]).natDegree ≤ 4 := by norm_num
theorem exact_uniform_family_domain :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W :=
  actual_weighted_uniform_o_one
end AFBoundary

run_cmd liftTermElabM do
  afRecord "typed_boundary" ``AFBoundary.factorial_lower_zero
  afRecord "typed_boundary" ``AFBoundary.factorial_upper_one
  afRecord "typed_boundary" ``AFBoundary.actual_n_one_k_one_zero
  afRecord "typed_boundary" ``AFBoundary.actual_n_one_k_two_positive
  afRecord "typed_boundary" ``AFBoundary.raw_n_one_first_term_zero
  afRecord "typed_boundary" ``AFBoundary.n_one_r_four_tail_exponent
  afRecord "typed_boundary" ``AFBoundary.n_one_compact_contains_only_zero
  afRecord "typed_boundary" ``AFBoundary.all_indices_nonnegative
  afRecord "typed_boundary" ``AFBoundary.no_even_input_for_actual_bound
  afRecord "typed_boundary" ``AFBoundary.zero_polynomial_series
  afRecord "typed_boundary" ``AFBoundary.zero_coefficient_height
  afRecord "typed_boundary" ``AFBoundary.negative_constant_has_domain
  afRecord "typed_boundary" ``AFBoundary.excluded_n_zero
  afRecord "typed_boundary" ``AFBoundary.excluded_degree_five
  afRecord "typed_boundary" ``AFBoundary.exact_uniform_family_domain
