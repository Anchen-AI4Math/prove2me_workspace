import Solutions.Sol_ZetaNine_CoefficientMapFiniteSum_harmonic_difference_eq_shifted
import Lean
open Lean Meta Polynomial Finset
open scoped BigOperators
open ZetaNine.CoefficientMapFiniteSum ZetaNine.CoefficientMapInjectivity
open ZetaNine.HarmonicStability
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false

theorem fs_review_actual_harmonic_definition (s N : ℕ) :
    harmonicPower s N = ∑ j ∈ Icc 1 N, 1 / (j : ℚ) ^ s := rfl

theorem fs_review_all_order_tail_at_zero (s j : ℕ) :
    harmonicPower s j = ∑ k ∈ Icc 1 j, 1 / (k : ℚ) ^ s := by
  simpa [harmonicPower] using solution s 0 j

theorem fs_review_empty_shift_at_any_order (s T : ℕ) :
    harmonicPower s (T + 0) - harmonicPower s T = 0 := by
  simpa using solution s T 0

theorem fs_review_order_zero_tail_keeps_shift_size (T j : ℕ) :
    harmonicPower 0 (T + j) - harmonicPower 0 T = (j : ℚ) := by
  simpa using solution 0 T j

theorem fs_review_finite_empty_without_properness (n : ℕ) (W : ℚ[X]) :
    finiteL n 0 W = 0 := by simp [finiteL]

theorem fs_review_tail_at_zero_exactly_cancels_B (n : ℕ) (W : ℚ[X]) :
    shiftedTail n 0 W = -constantTerm n W := by
  simp [shiftedTail, constantTerm, harmonicPower]

theorem fs_review_actual_zero_X_four_simple_function (t : ℚ) (ht : t ≠ 0) :
    ZetaNine.CoefficientMap.weightedR 0 ((X : ℚ[X]) ^ 4) t = 1 / t := by
  simp [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem fs_review_actual_simple_boundary_finite_sum (T : ℕ) :
    finiteL 0 T ((X : ℚ[X]) ^ 4) = harmonicPower 1 T := by
  unfold finiteL harmonicPower
  apply Finset.sum_congr rfl
  intro t ht
  have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  simpa using fs_review_actual_zero_X_four_simple_function (t : ℚ) (ne_of_gt htpos)

theorem fs_review_actual_simple_boundary_at_two :
    finiteL 0 2 ((X : ℚ[X]) ^ 4) = 3 / 2 := by
  rw [fs_review_actual_simple_boundary_finite_sum]
  norm_num [harmonicPower, Finset.sum_Icc_succ_top]

run_meta do
  for name in [
    `fs_review_actual_harmonic_definition,
    `fs_review_all_order_tail_at_zero,
    `fs_review_empty_shift_at_any_order,
    `fs_review_order_zero_tail_keeps_shift_size,
    `fs_review_finite_empty_without_properness,
    `fs_review_tail_at_zero_exactly_cancels_B,
    `fs_review_actual_zero_X_four_simple_function,
    `fs_review_actual_simple_boundary_finite_sum,
    `fs_review_actual_simple_boundary_at_two] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
