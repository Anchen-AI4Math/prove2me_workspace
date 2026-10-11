import Solutions.Sol_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper
import Lean

open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapInjectivity
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false

theorem review_strong_condition_is_two_degree_gap (n : ℕ) (W : ℚ[X]) :
    StrongProperMultiplier n W ↔ 2 * n + 2 * W.natDegree + 2 ≤ 9 * (n + 1) := by
  unfold StrongProperMultiplier
  omega

theorem review_strong_really_implies_proper (n : ℕ) (W : ℚ[X])
    (h : StrongProperMultiplier n W) : ProperMultiplier n W := by
  unfold StrongProperMultiplier at h
  unfold ProperMultiplier
  omega

theorem review_zero_boundary_is_proper_but_not_strong :
    ProperMultiplier 0 ((X : ℚ[X]) ^ 4) ∧
      ¬ StrongProperMultiplier 0 ((X : ℚ[X]) ^ 4) := by
  norm_num [ProperMultiplier, StrongProperMultiplier, Polynomial.natDegree_pow]

theorem review_actual_zero_local_series (W : ℚ[X]) :
    ZetaNine.CoefficientMapJet.weightedClearedSeries 0 0 W =
      (W.comp ((X : ℚ[X]) ^ 2) : PowerSeries ℚ) := by
  have hs : ZetaNine.CoefficientMapJet.clearedSeries 0 0 = 1 := by
    simp [ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator,
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator]
  have hu : ZetaNine.CoefficientMapJet.localU 0 0 = (X : ℚ[X]) ^ 2 := by
    simp [ZetaNine.CoefficientMapJet.localU,
      ZetaNine.CoefficientMapJet.shiftedVariable, pow_two]
  simp only [ZetaNine.CoefficientMapJet.weightedClearedSeries, hs, hu, one_mul]

theorem review_actual_zero_boundary_simple_coefficient :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient 0 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  rw [ZetaNine.CoefficientMapJet.weightedLocalCoefficient, review_actual_zero_local_series]
  simp only [Polynomial.pow_comp, Polynomial.X_comp, map_pow, Polynomial.coe_X]
  rw [← pow_mul]
  norm_num

theorem review_actual_zero_boundary_simple_total : rho 0 1 ((X : ℚ[X]) ^ 4) = 1 := by
  simpa [rho] using review_actual_zero_boundary_simple_coefficient

theorem review_even_total_without_properness :
    ¬ ProperMultiplier 0 ((X : ℚ[X]) ^ 5) ∧ rho 0 8 ((X : ℚ[X]) ^ 5) = 0 := by
  constructor
  · norm_num [ProperMultiplier, Polynomial.natDegree_pow]
  · exact rho_even_order_zero 0 8 (by norm_num) _ (by omega) (by omega) (by norm_num)

theorem review_one_quartic_is_strong_without_even (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    StrongProperMultiplier 1 W ∧ rho 1 1 W = 0 := by
  have h : StrongProperMultiplier 1 W := by unfold StrongProperMultiplier; omega
  exact ⟨h, checked_rho_one_zero_of_strong_proper 1 W h⟩

theorem review_actual_one_anti_reflection_fails :
    ZetaNine.CoefficientMap.weightedR 1 (1 : ℚ[X]) (-3) ≠
      -ZetaNine.CoefficientMap.weightedR 1 (1 : ℚ[X]) 2 := by
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct,
    Finset.prod_range_succ]

run_meta do
  for name in [
    `review_strong_condition_is_two_degree_gap,
    `review_strong_really_implies_proper,
    `review_zero_boundary_is_proper_but_not_strong,
    `review_actual_zero_local_series,
    `review_actual_zero_boundary_simple_coefficient,
    `review_actual_zero_boundary_simple_total,
    `review_even_total_without_properness,
    `review_one_quartic_is_strong_without_even,
    `review_actual_one_anti_reflection_fails] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
