import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-! A direct differential-operator certificate for the actual Franel gamma
identity. This file is developed independently of the coefficient-operator
file to avoid concurrent edits. No gamma expansion is used as a hypothesis. -/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

noncomputable section
open Polynomial
open scoped BigOperators

namespace ZetaNine.FranelGamma

def theta (p : ℚ[X]) : ℚ[X] := X * derivative p

def gammaBasis (k t : ℕ) : ℚ[X] := X ^ k * (1 + X) ^ t

def franelOperator (n : ℕ) (p : ℚ[X]) : ℚ[X] :=
  theta (theta (theta p)) + X * theta (theta (theta p)) -
    C (3 * (n : ℚ)) * X * theta (theta p) +
    C (3 * (n : ℚ) ^ 2) * X * theta p - C ((n : ℚ) ^ 3) * X * p

def franelPolynomial (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j ((n.choose j : ℚ) ^ 3)

def gammaCoefficient (n k : ℕ) : ℕ :=
  n.choose (2 * k) * (2 * k).choose k * (n + k).choose k

def gammaPolynomial (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k)

theorem theta_coeff (p : ℚ[X]) (j : ℕ) :
    (theta p).coeff j = (j : ℚ) * p.coeff j := by
  cases j with
  | zero => simp [theta]
  | succ j => simp [theta, Polynomial.coeff_X_mul, Polynomial.coeff_derivative, mul_comm]

theorem franelOperator_coeff_zero (n : ℕ) (p : ℚ[X]) :
    (franelOperator n p).coeff 0 = 0 := by
  simp [franelOperator, theta_coeff]

theorem franelOperator_coeff_succ (n : ℕ) (p : ℚ[X]) (j : ℕ) :
    (franelOperator n p).coeff (j + 1) =
      ((j : ℚ) + 1) ^ 3 * p.coeff (j + 1) -
        ((n : ℚ) - j) ^ 3 * p.coeff j := by
  simp only [franelOperator, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, theta_coeff,
    Nat.cast_add, Nat.cast_one]
  ring

theorem franelOperator_kernel_unique (n : ℕ) (p q : ℚ[X])
    (hp : franelOperator n p = 0) (hq : franelOperator n q = 0)
    (hzero : p.coeff 0 = q.coeff 0) : p = q := by
  ext j
  induction j with
  | zero => exact hzero
  | succ j ih =>
    have hpj := congrArg (fun f : ℚ[X] => f.coeff (j + 1)) hp
    have hqj := congrArg (fun f : ℚ[X] => f.coeff (j + 1)) hq
    simp only [franelOperator_coeff_succ, Polynomial.coeff_zero] at hpj hqj
    have hj : ((j : ℚ) + 1) ^ 3 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hj)
    rw [ih] at hpj
    linarith

theorem franelPolynomial_coeff (n j : ℕ) :
    (franelPolynomial n).coeff j = (n.choose j : ℚ) ^ 3 := by
  classical
  by_cases hj : j ≤ n
  · simp [franelPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Finset.mem_range, hj]
  · have hz := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)
    simp [franelPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Finset.mem_range, hj, hz]

theorem franelOperator_franelPolynomial (n : ℕ) :
    franelOperator n (franelPolynomial n) = 0 := by
  ext j
  cases j with
  | zero => exact franelOperator_coeff_zero n _
  | succ j =>
    simp only [franelOperator_coeff_succ, franelPolynomial_coeff, Polynomial.coeff_zero]
    by_cases hj : j ≤ n
    · have h : (n.choose (j + 1) : ℚ) * ((j : ℚ) + 1) =
          (n.choose j : ℚ) * ((n : ℚ) - j) := by
        have hn := Nat.choose_succ_right_eq n j
        have hcast := congrArg (fun x : ℕ => (x : ℚ)) hn
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using hcast
      nlinarith [congrArg (fun x : ℚ => x ^ 3) h]
    · have hz : n.choose j = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)
      have hzs : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz, hzs, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0),
        mul_zero, sub_self]

theorem theta_add (p q : ℚ[X]) : theta (p + q) = theta p + theta q := by
  simp [theta, mul_add]

theorem theta_C_mul (a : ℚ) (p : ℚ[X]) : theta (C a * p) = C a * theta p := by
  simp [theta, mul_left_comm]

theorem theta_X_pow (k : ℕ) : theta (X ^ k) = C (k : ℚ) * X ^ k := by
  cases k with
  | zero => simp [theta]
  | succ k =>
    rw [theta, Polynomial.derivative_X_pow_succ]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem theta_gammaBasis_succ (k t : ℕ) :
    theta (gammaBasis k (t + 1)) =
      C (k : ℚ) * gammaBasis k (t + 1) +
        C (t + 1 : ℚ) * gammaBasis (k + 1) t := by
  have hx := theta_X_pow k
  simp only [theta] at hx ⊢
  simp only [gammaBasis, Polynomial.derivative_mul, mul_add,
    Polynomial.derivative_pow_succ, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_X, zero_add, mul_one]
  rw [← mul_assoc, hx]
  simp only [pow_succ]
  ring

theorem theta_gammaBasis_zero (k : ℕ) :
    theta (gammaBasis k 0) = C (k : ℚ) * gammaBasis k 0 := by
  simp only [gammaBasis, pow_zero, mul_one, theta_X_pow]

theorem franelOperator_gammaBasis (k t : ℕ) :
    franelOperator (2 * k + t) (gammaBasis k t) =
      (1 - X) * (C ((k : ℚ) ^ 3) * gammaBasis k t -
        C (((3 * k + t + 1 : ℕ) : ℚ) * t * (t - 1 : ℕ)) *
          gammaBasis (k + 1) (t - 2)) := by
  unfold franelOperator
  cases t with
  | zero =>
    simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
      Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero,
      Nat.cast_mul, Nat.cast_ofNat]
    simp only [map_add, map_mul, map_ofNat, map_pow]
    ring
  | succ t =>
    cases t with
    | zero =>
      simp only [theta_gammaBasis_succ, theta_gammaBasis_zero, theta_add, theta_C_mul]
      simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero,
        Nat.sub_self, zero_mul, mul_zero, map_zero, add_zero, pow_succ]
      simp only [map_add, map_mul, map_one, map_zero, map_ofNat, map_pow]
      ring
    | succ t =>
      cases t with
      | zero =>
        simp only [theta_gammaBasis_succ, theta_gammaBasis_zero, theta_add, theta_C_mul]
        simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero,
          Nat.reduceSub, Nat.sub_self, zero_mul, mul_zero, map_zero, add_zero, pow_succ]
        simp only [map_add, map_mul, map_one, map_zero, map_ofNat, map_pow,
          Polynomial.C_1, Polynomial.C_0]
        norm_num
        ring
      | succ t =>
        simp only [theta_gammaBasis_succ, theta_add, theta_C_mul]
        simp only [gammaBasis, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, pow_succ]
        simp only [map_add, map_mul, map_one, map_ofNat, map_pow]
        ring

theorem gammaCoefficient_factorial (n k : ℕ) (hk : 2 * k ≤ n) :
    gammaCoefficient n k * k.factorial ^ 3 * (n - 2 * k).factorial =
      (n + k).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have heq : 2 * k - k = k := by omega
    simpa only [heq] using h
  have h3 : (n + k).choose k * k.factorial * n.factorial = (n + k).factorial := by
    simpa only [Nat.add_sub_cancel] using
      Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
  calc
    _ = (n + k).choose k * k.factorial *
        (n.choose (2 * k) * ((2 * k).choose k * k.factorial * k.factorial) *
          (n - 2 * k).factorial) := by unfold gammaCoefficient; ring
    _ = (n + k).choose k * k.factorial *
        (n.choose (2 * k) * (2 * k).factorial * (n - 2 * k).factorial) := by rw [h2]
    _ = (n + k).choose k * k.factorial * n.factorial := by rw [h1]
    _ = (n + k).factorial := h3

theorem gammaCoefficient_step (n k : ℕ) :
    (k + 1) ^ 3 * gammaCoefficient n (k + 1) =
      (n + k + 1) * (n - 2 * k) * (n - 2 * k - 1) * gammaCoefficient n k := by
  by_cases hk : 2 * k ≤ n
  · by_cases hks : 2 * (k + 1) ≤ n
    · have hfac : (n - 2 * k).factorial =
          (n - 2 * k) * (n - 2 * k - 1) * (n - 2 * (k + 1)).factorial := by
        have ht : n - 2 * k = (n - 2 * (k + 1)) + 2 := by omega
        have ht1 : n - 2 * k - 1 = (n - 2 * (k + 1)) + 1 := by omega
        rw [ht]
        rw [show n - 2 * (k + 1) + 2 - 1 = n - 2 * (k + 1) + 1 by omega]
        simp only [Nat.factorial_succ]
        ring
      have hnext := gammaCoefficient_factorial n (k + 1) hks
      have hprev := gammaCoefficient_factorial n k hk
      apply Nat.mul_right_cancel
        (show 0 < k.factorial ^ 3 * (n - 2 * (k + 1)).factorial by positivity)
      calc
        _ = gammaCoefficient n (k + 1) * (k + 1).factorial ^ 3 *
            (n - 2 * (k + 1)).factorial := by rw [Nat.factorial_succ]; ring
        _ = (n + (k + 1)).factorial := hnext
        _ = (n + k + 1) * (n + k).factorial := by
          change (n + k + 1).factorial = (n + k + 1) * (n + k).factorial
          exact Nat.factorial_succ (n + k)
        _ = (n + k + 1) *
            (gammaCoefficient n k * k.factorial ^ 3 * (n - 2 * k).factorial) := by rw [hprev]
        _ = _ := by rw [hfac]; ring
    · have hzero : n.choose (2 * (k + 1)) = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hks)
      have hsmall : n - 2 * k = 0 ∨ n - 2 * k = 1 := by omega
      rcases hsmall with hsmall | hsmall <;> simp [gammaCoefficient, hzero, hsmall]
  · have hzero : n.choose (2 * k) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    have hzeros : n.choose (2 * (k + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [gammaCoefficient, hzero, hzeros]

theorem franelOperator_C_mul (n : ℕ) (a : ℚ) (p : ℚ[X]) :
    franelOperator n (C a * p) = C a * franelOperator n p := by
  ext j
  cases j with
  | zero => simp [franelOperator_coeff_zero]
  | succ j =>
    simp only [franelOperator_coeff_succ, Polynomial.coeff_C_mul]
    ring

theorem franelOperator_sum {ι : Type*} (n : ℕ) (S : Finset ι) (f : ι → ℚ[X]) :
    franelOperator n (∑ i ∈ S, f i) = ∑ i ∈ S, franelOperator n (f i) := by
  ext j
  cases j with
  | zero => simp [franelOperator_coeff_zero, Polynomial.finsetSum_coeff]
  | succ j =>
    simp only [franelOperator_coeff_succ, Polynomial.finsetSum_coeff,
      Finset.mul_sum, Finset.sum_sub_distrib]

def gammaStep (n k : ℕ) : ℚ[X] :=
  C ((k : ℚ) ^ 3 * (gammaCoefficient n k : ℚ)) * gammaBasis k (n - 2 * k)

theorem franelOperator_gammaTerm (n k : ℕ) (hk : 2 * k ≤ n) :
    franelOperator n (C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k)) =
      (1 - X) * (gammaStep n k - gammaStep n (k + 1)) := by
  rw [franelOperator_C_mul]
  have hn : 2 * k + (n - 2 * k) = n := by omega
  have hgamma := franelOperator_gammaBasis k (n - 2 * k)
  rw [hn] at hgamma
  rw [hgamma]
  have hindex : 3 * k + (n - 2 * k) + 1 = n + k + 1 := by omega
  have htail : n - 2 * k - 2 = n - 2 * (k + 1) := by omega
  rw [hindex, htail]
  have hstep : ((k + 1 : ℕ) : ℚ) ^ 3 * (gammaCoefficient n (k + 1) : ℚ) =
      ((n + k + 1 : ℕ) : ℚ) * (n - 2 * k : ℕ) * (n - 2 * k - 1 : ℕ) *
        (gammaCoefficient n k : ℚ) := by
    exact_mod_cast gammaCoefficient_step n k
  unfold gammaStep
  rw [hstep]
  simp only [map_mul, map_pow]
  ring

theorem sum_range_difference (f : ℕ → ℚ[X]) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f k - f (k + 1))) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem franelOperator_gammaPolynomial (n : ℕ) :
    franelOperator n (gammaPolynomial n) = 0 := by
  classical
  rw [gammaPolynomial, franelOperator_sum]
  have hterms : (∑ k ∈ Finset.range (n / 2 + 1),
      franelOperator n (C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k))) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (1 - X) * (gammaStep n k - gammaStep n (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply franelOperator_gammaTerm
    have hk' := Finset.mem_range.mp hk
    omega
  rw [hterms, ← Finset.mul_sum, sum_range_difference]
  have hzero : n.choose (2 * (n / 2 + 1)) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [gammaStep, gammaCoefficient, hzero]

theorem gammaBasis_coeff_zero (k t : ℕ) :
    (gammaBasis k t).coeff 0 = if k = 0 then 1 else 0 := by
  simp [gammaBasis, Polynomial.coeff_X_pow_mul', Polynomial.coeff_one_add_X_pow,
    eq_comm]

theorem gammaPolynomial_coeff_zero (n : ℕ) :
    (gammaPolynomial n).coeff 0 = 1 := by
  classical
  simp [gammaPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    gammaBasis_coeff_zero, gammaCoefficient]

theorem franelPolynomial_eq_gammaPolynomial (n : ℕ) :
    franelPolynomial n = gammaPolynomial n := by
  apply franelOperator_kernel_unique n _ _
    (franelOperator_franelPolynomial n) (franelOperator_gammaPolynomial n)
  simp [franelPolynomial_coeff, gammaPolynomial_coeff_zero]

#print axioms franelOperator_kernel_unique
#print axioms franelOperator_franelPolynomial
#print axioms franelOperator_gammaBasis
#print axioms gammaCoefficient_step
#print axioms franelOperator_gammaPolynomial
#print axioms franelPolynomial_eq_gammaPolynomial

end ZetaNine.FranelGamma
