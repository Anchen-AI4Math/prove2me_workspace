import Oracle.CoefficientMapFormalTransportData

/-!
Basic actual-choice and strict proper-numerator bridge for formal transport.
The chosen pair is the genuine Connection witness, with n >= 1.  Gamma
recovers its actual quartic P.  The true cancellation numerator is zero at
t=2, including n=1, and is strictly proper in shifted coordinates when
deg(q)<=9.  This does not supply partial fractions or five-output transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace OutputsPlatformOracle.CoefficientMapFormalTransportBounds

open CoefficientMapFormalTransportData CoefficientMapConnection
open CoefficientMapAggregate CoefficientMapInjectivity

theorem connectionP_natDegree_le (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionP n r).natDegree ≤ 4 := (connectionPair_spec n hn r).1

theorem connectionQ_natDegree_le (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionQ n r).natDegree ≤ 9 := (connectionPair_spec n hn r).2.1

theorem chosen_connection_equation (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    connectionD n * (connectionP n r).comp (connectionU n) +
      connectionH n (connectionQ n r) =
        (connectionTarget n r.val).comp (connectionU n) :=
  (connectionPair_spec n hn r).2.2

theorem connectionGamma_row_coordinates (n : ℕ) (r : Fin 5) :
    connectionGamma n r = polynomialCoordinates (connectionP n r) := rfl

theorem connectionGamma_restores_P (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    coordinatePolynomial (connectionGamma n r) = connectionP n r := by
  rw [connectionGamma_row_coordinates]
  exact polynomial_restore _ (connectionP_natDegree_le n hn r)

theorem connectionP_eq_Gamma_row_sum (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    connectionP n r = ∑ l : Fin 5, C (connectionGamma n r l) * X ^ l.val :=
  (connectionGamma_restores_P n hn r).symm

theorem remainderNumerator_eval_two (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (remainderNumerator n q).eval 2 = 0 := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 2))).eval 2 = 0 := by
    simp only [eval_prod, eval_sub, eval_X, eval_C]
    apply Finset.prod_eq_zero (show 0 ∈ range n from mem_range.mpr (by omega))
    norm_num
  simp only [remainderNumerator, eval_mul, hL, mul_zero, zero_mul]

theorem shiftedRemainderNumerator_eval_one (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (shiftedRemainderNumerator n q).eval 1 = 0 := by
  simpa only [shiftedRemainderNumerator, eval_comp, eval_add, eval_X, eval_one,
    show (1 : ℚ) + 1 = 2 by norm_num] using remainderNumerator_eval_two n hn q

theorem connectionV_natDegree (n : ℕ) : (connectionV n).natDegree = 2 :=
  baseU_natDegree (n - 1)

theorem remainderNumerator_natDegree_le (n : ℕ) (q : ℚ[X]) :
    (remainderNumerator n q).natDegree ≤ 2 * n + 2 * q.natDegree := by
  have hL : (∏ i ∈ range n, (X - C ((i : ℚ) + 2))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X - C ((i : ℚ) + 2)).natDegree := natDegree_prod_le _ _
      _ = n := by
        simp only [natDegree_X_sub_C]
        simp
  have hR : (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))).natDegree ≤ n := by
    calc
      _ ≤ ∑ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1)).natDegree := natDegree_prod_le _ _
      _ = n := by
        simp only [natDegree_X_add_C]
        simp
  have h1 := natDegree_mul_le (p := C ((n.factorial : ℚ) ^ 7))
    (q := ∏ i ∈ range n, (X - C ((i : ℚ) + 2)))
  have h2 := natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))))
    (q := ∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1)))
  have h3 := natDegree_mul_le
    (p := C ((n.factorial : ℚ) ^ 7) * (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
      (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))))
    (q := q.comp (connectionV n))
  have hc := natDegree_comp_le (p := q) (q := connectionV n)
  rw [connectionV_natDegree] at hc
  simp only [natDegree_C, zero_add] at h1
  unfold remainderNumerator
  omega

theorem shiftedRemainderNumerator_natDegree_le (n : ℕ) (q : ℚ[X]) :
    (shiftedRemainderNumerator n q).natDegree ≤ 2 * n + 2 * q.natDegree := by
  have h := natDegree_comp_le (p := remainderNumerator n q) (q := X + 1)
  have hx : (X + 1 : ℚ[X]).natDegree = 1 := by
    simpa only [map_one] using (natDegree_X_add_C (1 : ℚ))
  rw [hx, Nat.mul_one] at h
  exact h.trans (remainderNumerator_natDegree_le n q)

theorem remainderNumerator_degree_nine_bound (n : ℕ) (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (remainderNumerator n q).natDegree ≤ 2 * n + 18 := by
  have h := remainderNumerator_natDegree_le n q
  omega

theorem shiftedRemainderNumerator_degree_nine_bound (n : ℕ) (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator n q).natDegree ≤ 2 * n + 18 := by
  have h := shiftedRemainderNumerator_natDegree_le n q
  omega

theorem remainderNumerator_strict_proper (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) : (remainderNumerator n q).natDegree < 9 * (n + 2) := by
  have h := remainderNumerator_degree_nine_bound n q hq
  omega

theorem shiftedRemainderNumerator_strict_proper (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) : (shiftedRemainderNumerator n q).natDegree < 9 * (n + 2) := by
  have h := shiftedRemainderNumerator_degree_nine_bound n q hq
  omega

theorem shiftedRemainderNumerator_below_pole_degree (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator n q).natDegree < (polePolynomial (n + 1) ^ 9).natDegree := by
  rw [polePolynomial_pow_natDegree]
  exact shiftedRemainderNumerator_strict_proper n hn q hq

theorem chosen_shifted_remainder_degree_bound (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (shiftedRemainderNumerator n (connectionQ n r)).natDegree ≤ 2 * n + 18 :=
  shiftedRemainderNumerator_degree_nine_bound n _ (connectionQ_natDegree_le n hn r)

theorem chosen_shifted_remainder_strict_proper (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (shiftedRemainderNumerator n (connectionQ n r)).natDegree < 9 * (n + 2) :=
  shiftedRemainderNumerator_strict_proper n hn _ (connectionQ_natDegree_le n hn r)

theorem boundary_n_one_zero (q : ℚ[X]) : (remainderNumerator 1 q).eval 2 = 0 :=
  remainderNumerator_eval_two 1 (by decide) q

theorem boundary_n_one_strict_proper (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (shiftedRemainderNumerator 1 q).natDegree < 27 := by
  exact shiftedRemainderNumerator_strict_proper 1 (by decide) q hq

end OutputsPlatformOracle.CoefficientMapFormalTransportBounds
