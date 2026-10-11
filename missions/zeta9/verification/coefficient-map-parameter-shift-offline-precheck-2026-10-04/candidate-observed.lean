import missions.zeta9.formalization.CoefficientMapKernelBridge
import missions.zeta9.formalization.CoefficientMapConnection

/-!
Actual n -> n+2 rational-function transport at regular rational points.
This is a candidate awaiting its first Lean compilation. It does not assert
transport of the five formal coefficient coordinates or an infinite sum.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapParameterShift

open CoefficientMapKernelBridge CoefficientMapConnection

def parameterScale (n : ℕ) : ℚ := (((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 7

def connectionRemainder (n : ℕ) (q : ℚ[X]) (t : ℚ) : ℚ :=
  CoefficientMap.actualR n t * (t - (n : ℚ) - 1) / (t - 1) ^ 10 *
    q.eval ((connectionV n).eval t)

theorem positiveProduct_add_two (n : ℕ) (t : ℚ) :
    positiveProduct (n + 2) t =
      positiveProduct n t * (t - (n : ℚ) - 1) * (t - (n : ℚ) - 2) := by
  unfold positiveProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast
  ring

theorem positiveProduct_parameter_shift (n : ℕ) (t : ℚ) :
    positiveProduct (n + 2) (t - 1) * (t - 1) =
      positiveProduct n t * (t - (n : ℚ) - 1) *
        (t - (n : ℚ) - 2) * (t - (n : ℚ) - 3) := by
  have h := positiveProduct_shift (n + 2) (t - 1)
  rw [sub_add_cancel, positiveProduct_add_two] at h
  push_cast at h
  calc
    _ = (t - 1) * positiveProduct (n + 2) (t - 1) := by ring
    _ = _ := by rw [← h]; ring

theorem negativeProduct_add_two_sub_one (n : ℕ) (t : ℚ) :
    negativeProduct (n + 2) (t - 1) = negativeProduct n (t + 1) *
      (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by
  unfold negativeProduct
  rw [Finset.prod_range_succ, Finset.prod_range_succ]
  have he : (∏ k ∈ range n, (t - 1 + ((n + 2 : ℕ) : ℚ) + ((k : ℚ) + 1))) =
      ∏ k ∈ range n, (t + 1 + (n : ℚ) + ((k : ℚ) + 1)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  push_cast
  ring

theorem negativeProduct_parameter_shift (n : ℕ) (t : ℚ) :
    negativeProduct (n + 2) (t - 1) * (t + (n : ℚ) + 1) =
      negativeProduct n t * (t + 2 * (n : ℚ) + 1) *
        (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by
  rw [negativeProduct_add_two_sub_one]
  calc
    _ = (negativeProduct n (t + 1) * (t + (n : ℚ) + 1)) *
        (t + 2 * (n : ℚ) + 2) * (t + 2 * (n : ℚ) + 3) := by ring
    _ = _ := by rw [negativeProduct_shift]

theorem poleProduct_parameter_shift (n : ℕ) (t : ℚ) :
    CoefficientMap.poleProduct (n + 2) (t - 1) =
      (t - 1) * CoefficientMap.poleProduct n t * (t + (n : ℚ) + 1) := by
  unfold CoefficientMap.poleProduct
  rw [Finset.prod_range_succ', Finset.prod_range_succ]
  have he : (∏ k ∈ range (n + 1), (t - 1 + ((k + 1 : ℕ) : ℚ))) =
      ∏ k ∈ range (n + 1), (t + (k : ℚ)) := by
    apply Finset.prod_congr rfl
    intro k hk
    push_cast
    ring
  rw [he]
  push_cast
  ring

theorem factorial_parameter_shift (n : ℕ) :
    ((n + 2).factorial : ℚ) ^ 7 = parameterScale n * (n.factorial : ℚ) ^ 7 := by
  rw [Nat.factorial_succ, Nat.factorial_succ]
  unfold parameterScale
  push_cast
  ring

theorem connectionZ_eval_factors (n : ℕ) (t : ℚ) :
    (connectionZ n).eval (t * (t + (n : ℚ))) =
      ((t - (n : ℚ) - 1) * (t + 2 * (n : ℚ) + 1)) *
        ((t - (n : ℚ) - 2) * (t + 2 * (n : ℚ) + 2)) *
        ((t - (n : ℚ) - 3) * (t + 2 * (n : ℚ) + 3)) := by
  simp only [connectionZ, eval_mul, eval_sub, eval_X, eval_C]
  ring

theorem numerator_parameter_shift (n : ℕ) (t : ℚ) :
    CoefficientMap.numerator (n + 2) (t - 1) * (t - 1) * (t + (n : ℚ) + 1) =
      parameterScale n * CoefficientMap.numerator n t *
        (connectionZ n).eval (t * (t + (n : ℚ))) := by
  change ((n + 2).factorial : ℚ) ^ 7 * positiveProduct (n + 2) (t - 1) *
      negativeProduct (n + 2) (t - 1) * (t - 1) * (t + (n : ℚ) + 1) =
    parameterScale n * ((n.factorial : ℚ) ^ 7 * positiveProduct n t * negativeProduct n t) * _
  rw [factorial_parameter_shift, connectionZ_eval_factors]
  calc
    _ = parameterScale n * (n.factorial : ℚ) ^ 7 *
        (positiveProduct (n + 2) (t - 1) * (t - 1)) *
        (negativeProduct (n + 2) (t - 1) * (t + (n : ℚ) + 1)) := by ring
    _ = _ := by rw [positiveProduct_parameter_shift, negativeProduct_parameter_shift]; ring

theorem connectionD_eval_factors (n : ℕ) (t : ℚ) :
    (connectionD n).eval t = (t - 1) ^ 10 * (t + (n : ℚ) + 1) ^ 10 := by
  rw [connectionD_factor]
  simp only [eval_mul, eval_pow, eval_sub, eval_add, eval_C, eval_X]
  ring

theorem shifted_regular_conditions (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    (∀ k ≤ n, t + (k : ℚ) ≠ 0) ∧
      (∀ k ≤ n, t + 1 + (k : ℚ) ≠ 0) ∧
        t - 1 ≠ 0 ∧ t ≠ 0 ∧ t + (n : ℚ) + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h := hregular (k + 1) (by omega)
    convert h using 1 <;> push_cast <;> ring
  · intro k hk
    have h := hregular (k + 2) (by omega)
    convert h using 1 <;> push_cast <;> ring
  · simpa using hregular 0 (by omega)
  · convert hregular 1 (by omega) using 1 <;> norm_num <;> ring
  · convert hregular (n + 2) (by omega) using 1 <;> push_cast <;> ring

theorem actual_R_parameter_shift (n : ℕ) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR (n + 2) (t - 1) * (connectionD n).eval t =
      parameterScale n * (connectionZ n).eval (t * (t + (n : ℚ))) *
        CoefficientMap.actualR n t := by
  obtain ⟨hreg, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  have hd := CoefficientMap.poleProduct_ne_zero n t hreg
  rw [connectionD_eval_factors]
  unfold CoefficientMap.actualR
  calc
    _ = (CoefficientMap.numerator (n + 2) (t - 1) * (t - 1) *
        (t + (n : ℚ) + 1)) / CoefficientMap.poleProduct n t ^ 9 := by
      rw [poleProduct_parameter_shift]
      field_simp [hm, hp, hd]
      ring
    _ = _ := by rw [numerator_parameter_shift]; ring

theorem connectionRemainder_successor (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    connectionRemainder n q (t + 1) =
      CoefficientMap.actualR n t * (t + 2 * (n : ℚ) + 1) /
        (t + (n : ℚ) + 1) ^ 10 * q.eval ((t + 1) * (t + (n : ℚ))) := by
  obtain ⟨hreg, hreg1, _, ht, hp⟩ := shifted_regular_conditions n t hregular
  have h := actual_R_shift_A_equals_R_B n t hreg hreg1
  have hv : (connectionV n).eval (t + 1) = (t + 1) * (t + (n : ℚ)) := by
    simp only [connectionV, eval_mul, eval_add, eval_X, eval_C, Nat.cast_sub hn, Nat.cast_one]
    ring
  unfold connectionRemainder
  rw [hv]
  have hs : t + 1 - 1 = t := by ring
  have ha : t + 1 - (n : ℚ) - 1 = t - (n : ℚ) := by ring
  rw [hs, ha]
  unfold aValue bValue at h
  have he : CoefficientMap.actualR n (t + 1) * (t - (n : ℚ)) /
      t ^ 10 = CoefficientMap.actualR n t * (t + 2 * (n : ℚ) + 1) /
        (t + (n : ℚ) + 1) ^ 10 := by
    apply (div_eq_div_iff (pow_ne_zero _ ht) (pow_ne_zero _ hp)).mpr
    convert h using 1 <;> ring
  rw [he]

theorem connectionRemainder_difference (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) (t : ℚ)
    (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    connectionRemainder n q t - connectionRemainder n q (t + 1) =
      CoefficientMap.actualR n t * (connectionH n q).eval t / (connectionD n).eval t := by
  obtain ⟨_, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  rw [connectionRemainder_successor n hn q t hregular, connectionRemainder,
    connectionD_eval_factors]
  simp only [connectionH, eval_sub, eval_mul, eval_pow, eval_add, eval_comp, eval_X, eval_C,
    eval_one, Nat.cast_add, Nat.cast_one]
  field_simp [hm, hp]
  ring

theorem actual_original_connection_transport (n : ℕ) (hn : 1 ≤ n) (r : ℕ)
    (P q : ℚ[X])
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q =
      (connectionTarget n r).comp (connectionU n))
    (t : ℚ) (hregular : ∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) :
    CoefficientMap.actualR (n + 2) (t - 1) *
        (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r =
      CoefficientMap.actualR n t * P.eval (t * (t + (n : ℚ))) +
        (connectionRemainder n q t - connectionRemainder n q (t + 1)) := by
  obtain ⟨_, _, hm, _, hp⟩ := shifted_regular_conditions n t hregular
  have hD : (connectionD n).eval t ≠ 0 := by
    rw [connectionD_eval_factors]
    exact mul_ne_zero (pow_ne_zero _ hm) (pow_ne_zero _ hp)
  have hpoly := congrArg (fun p : ℚ[X] => p.eval t) heq
  simp only [eval_add, eval_mul, eval_comp, connectionTarget, connectionU,
    eval_pow, eval_sub, eval_X, eval_C] at hpoly
  change (connectionD n).eval t * P.eval (t * (t + (n : ℚ))) +
      (connectionH n q).eval t = parameterScale n *
        (connectionZ n).eval (t * (t + (n : ℚ))) *
          (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r at hpoly
  have hR := actual_R_parameter_shift n t hregular
  rw [connectionRemainder_difference n hn q t hregular]
  apply (mul_right_cancel₀ hD)
  calc
    _ = (CoefficientMap.actualR (n + 2) (t - 1) * (connectionD n).eval t) *
        (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r := by ring
    _ = CoefficientMap.actualR n t *
        (parameterScale n * (connectionZ n).eval (t * (t + (n : ℚ))) *
          (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r) := by rw [hR]; ring
    _ = CoefficientMap.actualR n t *
        ((connectionD n).eval t * P.eval (t * (t + (n : ℚ))) + (connectionH n q).eval t) := by
      rw [← hpoly]
    _ = _ := by field_simp [hD]; ring

theorem five_actual_connection_transports_exist_unique (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) ∧
      ∀ t : ℚ, (∀ k ≤ n + 2, t - 1 + (k : ℚ) ≠ 0) →
        CoefficientMap.actualR (n + 2) (t - 1) *
            (t * (t + (n : ℚ)) - ((n : ℚ) + 1)) ^ r.val =
          CoefficientMap.actualR n t * pq.1.eval (t * (t + (n : ℚ))) +
            (connectionRemainder n pq.2 t - connectionRemainder n pq.2 (t + 1)) := by
  obtain ⟨pq, ⟨hP, hq, heq⟩, huniq⟩ := connection_five_systems_unique n hn r
  refine ⟨pq, ⟨hP, hq, heq, ?_⟩, ?_⟩
  · intro t hregular
    exact actual_original_connection_transport n hn r.val pq.1 pq.2 heq t hregular
  · intro pq' hpq'
    exact huniq pq' ⟨hpq'.1, hpq'.2.1, hpq'.2.2.1⟩

end ZetaNine.CoefficientMapParameterShift
