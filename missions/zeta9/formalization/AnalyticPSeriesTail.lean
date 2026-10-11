import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-!
UNCOMPILED SOURCE preparation. Quantitative tail for a genuine reciprocal
natural power series. Summability and the integral comparison are proved
from M >= 1 and s >= 2; neither is an input hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section
open scoped BigOperators
open Set MeasureTheory Finset

namespace ZetaNine.AnalyticPSeriesTail

theorem nat_negative_rpow_eq_reciprocal_pow (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := by
  rw [Real.rpow_neg (Nat.cast_nonneg k), Real.rpow_natCast, one_div]

theorem reciprocal_power_tail_summable (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := by
  exact (Real.summable_one_div_nat_pow.mpr (by omega : 1 < s)).comp_injective
    (fun _i _j h => Nat.add_right_cancel h)

theorem reciprocal_power_tail_bound (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs0 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < s - 1 by omega)
  have hsneg : -(s : ℝ) < -1 := by
    have h : (1 : ℝ) < s := by exact_mod_cast (show 1 < s by omega)
    linarith
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(s : ℝ))) (Ici (M : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by positivity : -(s : ℝ) ≤ 0)).mono
    intro x hx
    exact lt_of_lt_of_le hM0 hx
  have hint : IntegrableOn (fun x : ℝ => x ^ (-(s : ℝ))) (Ioi (M : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hsneg hM0
  have hnonneg : ∀ x ∈ Ioi (M : ℝ), 0 ≤ x ^ (-(s : ℝ)) := by
    intro x hx
    exact Real.rpow_nonneg (lt_trans hM0 hx).le _
  have htail := AntitoneOn.tsum_comp_add_le_integral M hanti hint hnonneg
  have heval := integral_Ioi_rpow_of_lt hsneg hM0
  have he : -(s : ℝ) + 1 = -((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    ring
  have heval' : (∫ x : ℝ in Ioi (M : ℝ), x ^ (-(s : ℝ))) =
      1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
    simpa only [he, nat_negative_rpow_eq_reciprocal_pow,
      div_neg, neg_div, neg_neg] using heval
  rw [heval'] at htail
  simp only [nat_negative_rpow_eq_reciprocal_pow] at htail
  have hsum := reciprocal_power_tail_summable M s hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have hsplit' : (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) =
      1 / (M : ℝ) ^ s + (∑' i : ℕ, 1 / ((i + M + 1 : ℕ) : ℝ) ^ s) := by
    simpa only [sum_range_one, Nat.zero_add, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hsplit.symm
  rw [hsplit']
  exact add_le_add_left htail _

theorem reciprocal_power_tail_bound_factored (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hs0 : (0 : ℝ) < ((s - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < s - 1 by omega)
  have hindex : s = s - 1 + 1 := by omega
  have hpow : (M : ℝ) ^ s = (M : ℝ) ^ (s - 1) * (M : ℝ) := by
    calc
      (M : ℝ) ^ s = (M : ℝ) ^ (s - 1 + 1) := by rw [← hindex]
      _ = _ := pow_succ _ _
  have he : 1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) =
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
    rw [hpow]
    field_simp [hM0.ne', hs0.ne']
    ring
  exact (reciprocal_power_tail_bound M s hM hs).trans_eq he

end ZetaNine.AnalyticPSeriesTail

#print axioms ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound
#print axioms ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored
