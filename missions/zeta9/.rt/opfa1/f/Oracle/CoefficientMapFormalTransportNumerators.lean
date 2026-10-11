import Oracle.CoefficientMapFormalTransportBounds
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite

/-!
Universal numerator transport for the actual chosen connection pair.

The actual chosen Connection pair supplies the polynomial equation.  The
proved ParameterShift identity is used only at positive regular rational
points.  Genuine product identities give the common denominator; infinitely
many such points then give the polynomial identity.  No PF-existence,
coefficient-transport, invertibility, parity or summation premise is added.
The finite independent probes are not used as proof evidence.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace OutputsPlatformOracle.CoefficientMapFormalTransportNumerators

open CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapKernelBridge CoefficientMapParameterShift
open CoefficientMapInjectivity CoefficientMapPartialFractions

theorem positiveProduct_remainder_cancellation (n : ℕ) (t : ℚ) :
    positiveProduct n t * (t - (n : ℚ) - 1) =
      (t - 1) * ∏ i ∈ range n, (t - ((i : ℚ) + 2)) := by
  have h := positiveProduct_shift n (t - 1)
  rw [sub_add_cancel] at h
  have he : positiveProduct n (t - 1) =
      ∏ i ∈ range n, (t - ((i : ℚ) + 2)) := by
    unfold positiveProduct
    apply Finset.prod_congr rfl
    intro i hi
    ring
  calc
    _ = positiveProduct n t * ((t - 1) - (n : ℚ)) := by ring
    _ = (t - 1) * positiveProduct n (t - 1) := h
    _ = _ := by rw [he]

theorem remainderNumerator_eval (n : ℕ) (q : ℚ[X]) (t : ℚ) :
    (remainderNumerator n q).eval t =
      (n.factorial : ℚ) ^ 7 *
        (∏ i ∈ range n, (t - ((i : ℚ) + 2))) *
        negativeProduct n t * q.eval ((CoefficientMapConnection.connectionV n).eval t) := by
  have he : (∏ i ∈ range n, (t + ((n : ℚ) + (i : ℚ) + 1))) =
      negativeProduct n t := by
    unfold negativeProduct
    apply Finset.prod_congr rfl
    intro i hi
    ring
  simp only [remainderNumerator, eval_mul, eval_prod, eval_sub,
    eval_add, eval_X, eval_C, eval_comp]
  rw [he]

theorem remainderNumerator_actual_cancellation (n : ℕ) (q : ℚ[X]) (t : ℚ) :
    CoefficientMap.numerator n t * (t - (n : ℚ) - 1) *
        q.eval ((CoefficientMapConnection.connectionV n).eval t) =
      (t - 1) * (remainderNumerator n q).eval t := by
  rw [remainderNumerator_eval]
  change (n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t *
      (t - (n : ℚ) - 1) * q.eval ((CoefficientMapConnection.connectionV n).eval t) = _
  calc
    _ = (n.factorial : ℚ) ^ 7 * (positiveProduct n t * (t - (n : ℚ) - 1)) *
        negativeProduct n t * q.eval ((CoefficientMapConnection.connectionV n).eval t) := by ring
    _ = _ := by rw [positiveProduct_remainder_cancellation]; ring

theorem connectionRemainder_as_actual_numerator (n : ℕ) (q : ℚ[X]) (t : ℚ)
    (hm : t - 1 ≠ 0) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    connectionRemainder n q t =
      (remainderNumerator n q).eval t /
        ((t - 1) * (polePolynomial n).eval t) ^ 9 := by
  have hd := CoefficientMap.poleProduct_ne_zero n t hregular
  rw [polePolynomial_eval]
  unfold connectionRemainder CoefficientMap.actualR
  calc
    _ = (CoefficientMap.numerator n t * (t - (n : ℚ) - 1) *
        q.eval ((CoefficientMapConnection.connectionV n).eval t)) /
        (CoefficientMap.poleProduct n t ^ 9 * (t - 1) ^ 10) := by
      field_simp [hm, hd]
      <;> ring
    _ = ((t - 1) * (remainderNumerator n q).eval t) /
        (CoefficientMap.poleProduct n t ^ 9 * (t - 1) ^ 10) := by
      rw [remainderNumerator_actual_cancellation]
    _ = _ := by
      field_simp [hm, hd]
      <;> ring

theorem polePolynomial_successor_eval (n : ℕ) (t : ℚ) :
    (polePolynomial (n + 1)).eval t =
      (polePolynomial n).eval t * (t + ((n : ℚ) + 1)) := by
  simp only [polePolynomial_eval, CoefficientMap.poleProduct]
  rw [Finset.prod_range_succ]
  simp only [Nat.cast_add, Nat.cast_one]

theorem polePolynomial_successor_shift_eval (n : ℕ) (x : ℚ) :
    (polePolynomial (n + 1)).eval x =
      x * (polePolynomial n).eval (x + 1) := by
  simp only [polePolynomial_eval, CoefficientMap.poleProduct]
  rw [Finset.prod_range_succ']
  have he : (∏ k ∈ range (n + 1), (x + ((k + 1 : ℕ) : ℚ))) =
      ∏ k ∈ range (n + 1), (x + 1 + (k : ℚ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  simp only [Nat.cast_zero, add_zero]
  ring

theorem polePolynomial_add_two_shift_eval (n : ℕ) (x : ℚ) :
    (polePolynomial (n + 2)).eval x =
      x * (polePolynomial n).eval (x + 1) * (x + ((n : ℚ) + 2)) := by
  have h := poleProduct_parameter_shift n (x + 1)
  rw [show x + 1 - 1 = x by ring] at h
  simp only [polePolynomial_eval]
  calc
    _ = x * CoefficientMap.poleProduct n (x + 1) * (x + 1 + (n : ℚ) + 1) := by
      simpa only [show x + 1 - 1 = x by ring] using h
    _ = _ := by ring

theorem polePolynomial_successor_shift (n : ℕ) :
    polePolynomial (n + 1) = X * (polePolynomial n).comp (X + 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  exact polePolynomial_successor_shift_eval n x

theorem polePolynomial_add_two_shift (n : ℕ) :
    polePolynomial (n + 2) =
      X * (polePolynomial n).comp (X + 1) * (X + C ((n : ℚ) + 2)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one, eval_C]
  exact polePolynomial_add_two_shift_eval n x

theorem connectionRemainder_shifted_as_actual_numerator (n : ℕ) (q : ℚ[X]) (x : ℚ)
    (hregular : ∀ k ≤ n + 1, x + (k : ℚ) ≠ 0) :
    connectionRemainder n q (x + 1) =
      (shiftedRemainderNumerator n q).eval x / (polePolynomial (n + 1)).eval x ^ 9 := by
  have hx : x ≠ 0 := by simpa using hregular 0 (by omega)
  have hm : x + 1 - 1 ≠ 0 := by simpa only [add_sub_cancel_right] using hx
  have hreg : ∀ k ≤ n, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    have h := hregular (k + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring
  calc
    _ = (remainderNumerator n q).eval (x + 1) /
        ((x + 1 - 1) * (polePolynomial n).eval (x + 1)) ^ 9 :=
      connectionRemainder_as_actual_numerator n q (x + 1) hm hreg
    _ = _ := by
      rw [shiftedRemainderNumerator, eval_comp, eval_add, eval_X, eval_one,
        polePolynomial_successor_shift_eval]
      rw [show x + 1 - 1 = x by ring]

theorem connectionRemainder_eval_two (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    connectionRemainder n q 2 = 0 := by
  have hregular : ∀ k ≤ n, (2 : ℚ) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  rw [connectionRemainder_as_actual_numerator n q 2 (by norm_num) hregular,
    remainderNumerator_eval_two n hn q, zero_div]

theorem actual_chosen_connection_transport_positive (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x) :
    CoefficientMap.weightedR (n + 2) (X ^ r.val) x =
      CoefficientMap.weightedR n (connectionP n r) (x + 1) +
        (connectionRemainder n (connectionQ n r) (x + 1) -
          connectionRemainder n (connectionQ n r) (x + 1 + 1)) := by
  have hregular : ∀ k ≤ n + 2, x + 1 - 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    rw [show x + 1 - 1 = x by ring]
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k))
  have hu : (x + 1) * (x + 1 + (n : ℚ)) - ((n : ℚ) + 1) =
      x * (x + ((n + 2 : ℕ) : ℚ)) := by
    push_cast
    ring
  have h := actual_original_connection_transport n hn r.val (connectionP n r)
    (connectionQ n r) (chosen_connection_equation n hn r) (x + 1) hregular
  simpa only [CoefficientMap.weightedR, eval_pow, eval_X, hu,
    show x + 1 - 1 = x by ring] using h

private theorem three_denominator_combination (B C D x y M : ℚ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hM : M ≠ 0) :
    B / M ^ 9 + (C / (x * M) ^ 9 - D / (M * y) ^ 9) =
      (x ^ 9 * y ^ 9 * B + y ^ 9 * C - x ^ 9 * D) / (x * M * y) ^ 9 := by
  field_simp [hx, hy, hM]
  <;> ring

theorem actual_chosen_cleared_numerator_transport_eval (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x) :
    (weightedNumerator (n + 2) (X ^ r.val)).eval x =
      x ^ 9 * (x + ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).eval (x + 1) +
        (x + ((n : ℚ) + 2)) ^ 9 *
          (shiftedRemainderNumerator n (connectionQ n r)).eval x -
        x ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).eval (x + 1) := by
  have hreg : ∀ k ≤ n + 1, x + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg k))
  have hreg1 : ∀ k ≤ n + 1, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hregOld : ∀ k ≤ n, x + 1 + (k : ℚ) ≠ 0 := by
    intro k hk
    exact hreg1 k (by omega)
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : x + ((n : ℚ) + 2) ≠ 0 := ne_of_gt (by positivity)
  have hM : (polePolynomial n).eval (x + 1) ≠ 0 :=
    polePolynomial_eval_ne_zero n (x + 1) hregOld
  have hright : (polePolynomial (n + 1)).eval (x + 1) =
      (polePolynomial n).eval (x + 1) * (x + ((n : ℚ) + 2)) := by
    rw [polePolynomial_successor_eval]
    ring
  have h := actual_chosen_connection_transport_positive n hn r x hx
  rw [actual_weighted_rational_representation, actual_weighted_rational_representation,
    connectionRemainder_shifted_as_actual_numerator n (connectionQ n r) x hreg,
    connectionRemainder_shifted_as_actual_numerator n (connectionQ n r) (x + 1) hreg1,
    polePolynomial_add_two_shift_eval n x,
    polePolynomial_successor_shift_eval n x, hright] at h
  rw [three_denominator_combination
    ((weightedNumerator n (connectionP n r)).eval (x + 1))
    ((shiftedRemainderNumerator n (connectionQ n r)).eval x)
    ((shiftedRemainderNumerator n (connectionQ n r)).eval (x + 1))
    x (x + ((n : ℚ) + 2)) ((polePolynomial n).eval (x + 1)) hx0 hy0 hM] at h
  exact (div_left_inj' (pow_ne_zero 9 (mul_ne_zero (mul_ne_zero hx0 hM) hy0))).mp h

/-- Actual universal polynomial transport, with the chosen pair and no relation premise. -/
theorem actual_chosen_cleared_numerator_transport (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    weightedNumerator (n + 2) (X ^ r.val) =
      X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).comp (X + 1) +
        (X + C ((n : ℚ) + 2)) ^ 9 *
          shiftedRemainderNumerator n (connectionQ n r) -
        X ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).comp (X + 1) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.Ioi_infinite (0 : ℚ)).mono
  intro x hx
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_comp, eval_one]
  exact actual_chosen_cleared_numerator_transport_eval n hn r x hx

end OutputsPlatformOracle.CoefficientMapFormalTransportNumerators
