import CoefficientMap

set_option autoImplicit false
open scoped BigOperators
open Polynomial ZetaNine.CoefficientMap

namespace ZetaNine.CoefficientMapIndependentReview

theorem regular_clearing (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    actualR n t * (t + j) ^ 9 =
      numerator n t / (∏ k ∈ (Finset.range (n + 1)).erase j, (t + k)) ^ 9 := by
  exact clear_highest_pole n j hj t ht

theorem deleted_denominator_nonzero (n j : ℕ) :
    (∏ k ∈ (Finset.range (n + 1)).erase j, (-(j : ℚ) + k)) ≠ 0 := by
  exact clearedPoleProduct_ne_zero n j

theorem computed_highest_coefficient (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) :=
  leadingPoleCoefficient_eq n j hj

theorem actual_weighted_multiplier (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      leadingPoleCoefficient n j * W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  rw [weightedLeadingPoleCoefficient_eq n j hj W, leadingPoleCoefficient_eq n j hj]

theorem weighted_nonzero_iff (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W ≠ 0 ↔
      W.eval (-(j : ℚ) * (n - j : ℕ)) ≠ 0 := by
  rw [actual_weighted_multiplier n j hj W]
  constructor
  · intro h
    exact (mul_ne_zero_iff.mp h).2
  · intro h
    exact mul_ne_zero (leadingPoleCoefficient_ne_zero n j hj) h

theorem zero_boundary_coefficient : leadingPoleCoefficient 0 0 = 1 := by
  norm_num [leadingPoleCoefficient, clearedR, clearedPoleProduct, numerator]

theorem odd_left_sign : leadingPoleCoefficient 1 0 = -2 := by
  have hset : (Finset.range 2).erase 0 = {1} := by decide
  norm_num [leadingPoleCoefficient, clearedR, clearedPoleProduct, numerator,
    Finset.prod_range_succ, hset]

theorem odd_right_sign : leadingPoleCoefficient 1 1 = 2 := by
  norm_num [leadingPoleCoefficient, clearedR, clearedPoleProduct, numerator,
    Finset.range_add_one]

theorem even_middle_value : leadingPoleCoefficient 2 1 = -4608 := by
  norm_num [leadingPoleCoefficient_eq, show (1 : ℕ) ≤ 2 by omega]

theorem nonzero_polynomial_cancels_top_pole :
    weightedLeadingPoleCoefficient 2 1 (X + 1 : ℚ[X]) = 0 := by
  rw [actual_weighted_multiplier 2 1 (by omega)]
  norm_num

#print numerator
#print poleProduct
#print actualR
#print clearedR
#print leadingPoleCoefficient
#print weightedLeadingPoleCoefficient
#check @leadingPoleCoefficient_is_integer
#check @signed_leadingPoleCoefficient_pos_even
#check @local_coordinate_identity
#check @weightedLeadingPoleCoefficient_eq_even

#print axioms regular_clearing
#print axioms deleted_denominator_nonzero
#print axioms computed_highest_coefficient
#print axioms actual_weighted_multiplier
#print axioms weighted_nonzero_iff
#print axioms zero_boundary_coefficient
#print axioms odd_left_sign
#print axioms odd_right_sign
#print axioms even_middle_value
#print axioms nonzero_polynomial_cancels_top_pole

end ZetaNine.CoefficientMapIndependentReview
