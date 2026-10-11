import Solutions.Sol_ZetaNine_CoefficientMapShiftDegree_actual_shift_difference_small_degree_implies_zero
import Lean
open Lean Meta Polynomial
open ZetaNine.CoefficientMapShiftDegree
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2000000

theorem checked_actual_operator_eval (n : ℕ) (H : ℚ[X]) (t : ℚ) :
    (shiftDifference n H).eval t =
      (t - ((n : ℚ) + 1)) * (t + (n : ℚ)) ^ 10 * H.eval t -
      t ^ 10 * (t + (2 * (n : ℚ) + 1)) * H.eval (t + 1) := by
  simp [shiftDifference, shiftA, shiftB, eval_comp]

theorem checked_degree_zero_shift (H : ℚ[X]) (hH : H.natDegree = 0) :
    H.comp (X + C 1) = H := by
  rw [eq_C_of_natDegree_eq_zero hH]
  simp

theorem checked_n_one_constant_coefficient :
    (shiftDifference 1 (1 : ℚ[X])).coeff 10 = 5 := by
  have h := actual_shift_difference_coefficient 1 (1 : ℚ[X]) one_ne_zero
  norm_num at h
  exact h

theorem checked_n_one_last_allowed_coefficient :
    (shiftDifference 1 (X ^ 4 : ℚ[X])).coeff 14 = 1 := by
  have h := actual_shift_difference_coefficient 1 (X ^ 4 : ℚ[X]) (pow_ne_zero 4 X_ne_zero)
  norm_num at h
  exact h

theorem checked_n_one_resonance_outside_domain :
    (shiftDifference 1 (X ^ 5 : ℚ[X])).coeff 15 = 0 ∧
      (X ^ 5 : ℚ[X]) ≠ 0 ∧ ¬ (X ^ 5 : ℚ[X]).natDegree ≤ 7 * 1 - 3 := by
  have h := actual_shift_difference_coefficient 1 (X ^ 5 : ℚ[X]) (pow_ne_zero 5 X_ne_zero)
  norm_num at h
  exact ⟨h, pow_ne_zero 5 X_ne_zero, by norm_num⟩

theorem checked_n_two_nonmonic_last_allowed :
    (shiftDifference 2 (C 7 * X ^ 11 : ℚ[X])).coeff 21 = 7 := by
  have hC : (C 7 : ℚ[X]) ≠ 0 := by norm_num
  have hX : (X ^ 11 : ℚ[X]) ≠ 0 := pow_ne_zero 11 X_ne_zero
  have hdeg : (C 7 * X ^ 11 : ℚ[X]).natDegree = 11 := by
    rw [natDegree_mul hC hX]
    simp
  have hlead : (C 7 * X ^ 11 : ℚ[X]).leadingCoeff = 7 := by simp [leadingCoeff_mul]
  have h := actual_shift_difference_coefficient 2 (C 7 * X ^ 11 : ℚ[X]) (mul_ne_zero hC hX)
  norm_num [hdeg, hlead] at h
  exact h

theorem checked_exact_kernel_degree_interface (n : ℕ) (hn : 1 ≤ n) (H : ℚ[X])
    (hdeg : H.natDegree ≤ 7 * n - 3)
    (hsmall : (shiftDifference n H).natDegree ≤ 8) : H = 0 :=
  checked_actual_shift_difference_small_degree_implies_zero n hn H hdeg hsmall

run_meta do
  for name in [
    `ZetaNine.CoefficientMapShiftDegree.shiftA,
    `ZetaNine.CoefficientMapShiftDegree.shiftB,
    `ZetaNine.CoefficientMapShiftDegree.shiftDifference,
    `ZetaNine.CoefficientMapShiftDegree.actual_nextCoeff_mul,
    `ZetaNine.CoefficientMapShiftDegree.actual_shift_nextCoeff,
    `ZetaNine.CoefficientMapShiftDegree.shiftA_monic,
    `ZetaNine.CoefficientMapShiftDegree.shiftB_monic,
    `ZetaNine.CoefficientMapShiftDegree.shiftA_natDegree,
    `ZetaNine.CoefficientMapShiftDegree.shiftB_natDegree,
    `ZetaNine.CoefficientMapShiftDegree.shiftA_nextCoeff,
    `ZetaNine.CoefficientMapShiftDegree.shiftB_nextCoeff,
    `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient,
    `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_coefficient_ne_zero,
    `ZetaNine.CoefficientMapShiftDegree.actual_shift_difference_degree_lower_bound,
    `ZetaNine.CoefficientMapShiftDegree.checked_actual_shift_difference_small_degree_implies_zero,
    `checked_actual_operator_eval,
    `checked_degree_zero_shift,
    `checked_n_one_constant_coefficient,
    `checked_n_one_last_allowed_coefficient,
    `checked_n_one_resonance_outside_domain,
    `checked_n_two_nonmonic_last_allowed,
    `checked_exact_kernel_degree_interface] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("type",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString)),("definitionValue",value)]).compress
