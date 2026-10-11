import missions.zeta9.formalization.CoefficientMapAggregate
import Lean
open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapReflection
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

theorem checked_five_actual_coordinates (n : ℕ) (W : ℚ[X]) :
    aggregate n W 0 = ZetaNine.CoefficientMapFiniteSum.constantTerm n W ∧
    aggregate n W 1 = ZetaNine.CoefficientMapFiniteSum.rho n 3 W ∧
    aggregate n W 2 = ZetaNine.CoefficientMapFiniteSum.rho n 5 W ∧
    aggregate n W 3 = ZetaNine.CoefficientMapFiniteSum.rho n 7 W ∧
    aggregate n W 4 = ZetaNine.CoefficientMapFiniteSum.rho n 9 W :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem checked_actual_monomial_basis (i : Fin 5) :
    coordinatePolynomial (Pi.single i (1 : ℚ)) = X ^ i.val := by
  classical
  unfold coordinatePolynomial
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem checked_basis_columns (n : ℕ) (i : Fin 5) :
    quarticAggregateLinearMap n (Pi.single i (1 : ℚ)) = aggregate n (X ^ i.val) := by
  rw [quartic_aggregate_is_actual, checked_actual_monomial_basis]

theorem checked_n_zero_X_four_aggregate_kernel :
    aggregate 0 (X ^ 4 : ℚ[X]) = 0 ∧ (X ^ 4 : ℚ[X]) ≠ 0 ∧
    ZetaNine.CoefficientMapInjectivity.ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
    ¬ StrongProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
    ZetaNine.CoefficientMapReflection.rho 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  have hkernel : aggregate 0 (X ^ 4 : ℚ[X]) = 0 := by
    funext i
    fin_cases i <;> norm_num [aggregate, ZetaNine.CoefficientMapFiniteSum.constantTerm,
      ZetaNine.CoefficientMapFiniteSum.rho, ZetaNine.HarmonicStability.harmonicPower,
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
      ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← pow_two, ← pow_mul]
  refine ⟨hkernel, pow_ne_zero 4 X_ne_zero, ?_, ?_, ?_⟩
  · norm_num [ZetaNine.CoefficientMapInjectivity.ProperMultiplier]
  · norm_num [StrongProperMultiplier]
  · norm_num [ZetaNine.CoefficientMapReflection.rho, ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
      ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_original_quartic_zero_all_orders (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) :
    ∀ s, 1 ≤ s → s ≤ 9 →
      (∑ j ∈ range (n + 1), ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W) = 0 := by
  intro s hs1 hs9
  exact aggregate_zero_all_rho n hn W (quartic_is_strong_proper n (by omega) W hW) hzero s hs1 hs9

theorem checked_original_quartic_zero_exact_sum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℚ[X]) (hW : W.natDegree ≤ 4) (hzero : aggregate n W = 0) :
    HasSum (fun t : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ)) 0 := by
  have h := ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL n hn W
    (quartic_is_strong_proper n (by omega) W hW)
  rw [aggregate_zero_exactL n W hzero] at h
  exact h

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
  for name in [
    `ZetaNine.CoefficientMapAggregate.aggregate,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial,
    `ZetaNine.CoefficientMapAggregate.polynomialCoordinates,
    `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_add,
    `ZetaNine.CoefficientMapAggregate.actual_local_coefficient_smul,
    `ZetaNine.CoefficientMapAggregate.actual_rho_add,
    `ZetaNine.CoefficientMapAggregate.actual_rho_smul,
    `ZetaNine.CoefficientMapAggregate.actual_constant_add,
    `ZetaNine.CoefficientMapAggregate.actual_constant_smul,
    `ZetaNine.CoefficientMapAggregate.aggregate_add,
    `ZetaNine.CoefficientMapAggregate.aggregate_smul,
    `ZetaNine.CoefficientMapAggregate.aggregateLinearMap,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_add,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_smul,
    `ZetaNine.CoefficientMapAggregate.coordinateLinearMap,
    `ZetaNine.CoefficientMapAggregate.quarticAggregateLinearMap,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_coeff,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_coeff_above,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_natDegree_le,
    `ZetaNine.CoefficientMapAggregate.coordinates_restore,
    `ZetaNine.CoefficientMapAggregate.polynomial_restore,
    `ZetaNine.CoefficientMapAggregate.coordinatePolynomial_injective,
    `ZetaNine.CoefficientMapAggregate.quartic_aggregate_is_actual,
    `ZetaNine.CoefficientMapAggregate.aggregate_zero_iff,
    `ZetaNine.CoefficientMapAggregate.aggregate_zero_all_rho,
    `ZetaNine.CoefficientMapAggregate.aggregate_zero_exactL,
    `checked_five_actual_coordinates,
    `checked_actual_monomial_basis,
    `checked_basis_columns,
    `checked_n_zero_X_four_aggregate_kernel,
    `checked_original_quartic_zero_all_orders,
    `checked_original_quartic_zero_exact_sum] do emit name
