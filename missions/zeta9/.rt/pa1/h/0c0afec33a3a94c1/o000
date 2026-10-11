import missions.zeta9.formalization.CoefficientMapPartialFractions
import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Algebra.BigOperators.Intervals

/-!
The actual finite summation bridge for the p=9, m=n family.
All coefficients come from the genuine local series. The simple-pole
harmonic term is retained. No infinite sum or irrationality is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFiniteSum

open HarmonicStability CoefficientMapInjectivity CoefficientMapPartialFractions

def rho (n s : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), CoefficientMapJet.weightedLocalCoefficient n j s W

def constantTerm (n : ℕ) (W : ℚ[X]) : ℚ :=
  -(∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s j)

def finiteL (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ t ∈ Icc 1 T, CoefficientMap.weightedR n W (t : ℚ)

def shiftedTail (n T : ℕ) (W : ℚ[X]) : ℚ :=
  ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
    CoefficientMapJet.weightedLocalCoefficient n j s W *
      (harmonicPower s (T + j) - harmonicPower s T)

theorem harmonicPower_succ (s T : ℕ) :
    harmonicPower s (T + 1) = harmonicPower s T + 1 / ((T + 1 : ℕ) : ℚ) ^ s := by
  unfold harmonicPower
  exact Finset.sum_Icc_succ_top (by omega) _

theorem shifted_harmonic_sum (s T j : ℕ) :
    (∑ t ∈ Icc 1 T, 1 / ((t : ℚ) + (j : ℚ)) ^ s) =
      harmonicPower s (T + j) - harmonicPower s j := by
  induction T with
  | zero => simp [harmonicPower]
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have he : T + 1 + j = (T + j) + 1 := by omega
    rw [he, harmonicPower_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

theorem actual_finite_harmonic_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      CoefficientMapJet.weightedLocalCoefficient n j s W *
        (harmonicPower s (T + j) - harmonicPower s j) := by
  unfold finiteL
  calc
    _ = ∑ t ∈ Icc 1 T, ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro t ht
      apply actual_global_partial_fractions n W hproper
      intro k hk
      have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
      exact ne_of_gt (add_pos_of_pos_of_nonneg htpos (Nat.cast_nonneg k))
    _ = ∑ j ∈ range (n + 1), ∑ t ∈ Icc 1 T, ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s :=
      Finset.sum_comm
    _ = ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9, ∑ t ∈ Icc 1 T,
        CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro j hj
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro s hs
      have hterm : (∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W / ((t : ℚ) + (j : ℚ)) ^ s) =
          ∑ t ∈ Icc 1 T,
          CoefficientMapJet.weightedLocalCoefficient n j s W * (1 / ((t : ℚ) + (j : ℚ)) ^ s) := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
      rw [hterm]
      rw [← Finset.mul_sum, shifted_harmonic_sum]

theorem actual_grouped_finite_identity (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_finite_harmonic_identity n T W hproper]
  have hmain : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        CoefficientMapJet.weightedLocalCoefficient n j s W * harmonicPower s T := by
    unfold rho
    simp only [Finset.sum_mul]
    exact Finset.sum_comm
  rw [hmain]
  unfold constantTerm shiftedTail
  simp only [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  ring

-- Cancellation is an explicit input here; the reflection development proves it.
-- In particular, properness alone does not supply the simple-pole cancellation.
theorem actual_grouped_finite_identity_no_simple_pole (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (hcancel : rho n 1 W = 0) :
    finiteL n T W = constantTerm n W +
      (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) + shiftedTail n T W := by
  rw [actual_grouped_finite_identity n T W hproper]
  have hsplit : (∑ s ∈ Icc 1 9, rho n s W * harmonicPower s T) =
      rho n 1 W * harmonicPower 1 T + ∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    rfl
  rw [hsplit, hcancel, zero_mul, zero_add]

theorem actual_grouped_finite_identity_odd (n T : ℕ) (W : ℚ[X])
    (hproper : ProperMultiplier n W) (h1 : rho n 1 W = 0)
    (h2 : rho n 2 W = 0) (h4 : rho n 4 W = 0)
    (h6 : rho n 6 W = 0) (h8 : rho n 8 W = 0) :
    finiteL n T W = constantTerm n W +
      (rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
       rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T) +
      shiftedTail n T W := by
  rw [actual_grouped_finite_identity_no_simple_pole n T W hproper h1]
  have hs : (∑ s ∈ Icc 2 9, rho n s W * harmonicPower s T) =
      rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
      rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T := by
    norm_num [Finset.sum_Icc_succ_top, h2, h4, h6, h8]
  rw [hs]

theorem harmonic_difference_eq_shifted (s T j : ℕ) :
    harmonicPower s (T + j) - harmonicPower s T =
      ∑ k ∈ Icc 1 j, 1 / ((T : ℚ) + (k : ℚ)) ^ s := by
  simpa only [Nat.add_comm j T, add_comm] using (shifted_harmonic_sum s j T).symm

end ZetaNine.CoefficientMapFiniteSum

#print axioms ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum
#print axioms ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity
#print axioms ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity
#print axioms ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole
#print axioms ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd
#print axioms ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted
