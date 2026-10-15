import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.quartic_switch_bounds (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    phi t ≤ gamma 232 t ∧ 0 < phiDeriv t ∧ phiDeriv t < 9 ∧
    phi tangentPoint + (t - tangentPoint) * phiDeriv tangentPoint ≤ phi t := by sorry

theorem ThreeSum1960614.uniform_entropy_bound (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    entropy t < rho * (1 + phi t) := by sorry

theorem ThreeSum1960614.quartic_parameter_certificate :
    4648781151243719 / 1000000000000000 < E 232 ∧
    E 232 < 4648781151243720 / 1000000000000000 ∧
    1557987216578 / 1000000000000000 < kappa 232 ∧
    kappa 232 < 1557987216579 / 1000000000000000 ∧
    entropy theta < 244168414687344 / 1000000000000000 ∧
    v < phi theta ∧ threshold tau < phi (1 / 2) ∧
    0 < epsilon * (E 232 + beta) ∧ epsilon * (E 232 + beta) < 1 ∧
    (∀ z ∈ costs, z < principal) ∧ principal < (target : ℝ) := by sorry

theorem ThreeSum1960614.integer_schedule (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s) := by sorry

theorem ThreeSum1960614.local_cover_bounds (c h : ℕ)
    (hc : 3 ≤ c) (hh : 0 < h) :
    Nat.choose (c * (2 * h)) h * Nat.choose (c * (2 * h) - h) h =
      Nat.choose (c * (2 * h)) (2 * h) * Nat.choose (2 * h) h ∧
    Nat.choose (c * (2 * h) - h) h ≤ Nat.choose (c * (2 * h)) h ∧
    Nat.choose (2 * h) h < 2 ^ (2 * h) ∧
    2 ^ (2 * h) < Nat.choose (c * (2 * h)) (2 * h) ∧
    Nat.choose (c * (2 * h) - h) h ^ 2 <
      Nat.choose (c * (2 * h)) (2 * h) * 2 ^ (2 * h) := by sorry

theorem ThreeSum1960614.fixed_model_lower_bound
    (e b S th terminal ratio R : ℝ)
    (hmodel : ModelFeasible 232 e b S th terminal ratio R) :
    (196061349120 / 100000000000 : ℝ) < R := by sorry

theorem ThreeSum1960614.costs_solve_3sum (r : ℚ)
    (hr : 0 < r) (hcost : ∀ z ∈ costs, z < (r : ℝ)) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry

theorem ThreeSum1960614.threeSum_1960614 :
    EndStatement.ThreeSum.SolvedInTime 1.960614 := by sorry
