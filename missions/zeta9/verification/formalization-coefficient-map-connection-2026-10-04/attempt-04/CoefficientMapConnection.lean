import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! The polynomial homogeneous kernel underlying the round-seven connection.
This source has no dependence on zeta values, aggregate maps or a kernel hypothesis. -/

noncomputable section
open Polynomial

namespace ZetaNine.CoefficientMapConnection

def connectionU (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))

def connectionV (n : ℕ) : ℚ[X] := X * (X + C ((n - 1 : ℕ) : ℚ))

def connectionD (n : ℕ) : ℚ[X] := (connectionU n - C ((n : ℚ) + 1)) ^ 10

def connectionH (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10 * q.comp (connectionV n) -
    (X + C (2 * (n : ℚ) + 1)) * (X - 1) ^ 10 *
      q.comp ((X + 1) * (X + C (n : ℚ)))

theorem connectionD_factor (n : ℕ) :
    connectionD n = (X - C (1 : ℚ)) ^ 10 * (X + C ((n : ℚ) + 1)) ^ 10 := by
  unfold connectionD connectionU
  have h : X * (X + C (n : ℚ)) - C ((n : ℚ) + 1) =
      (X - C (1 : ℚ)) * (X + C ((n : ℚ) + 1)) := by
    simp only [map_add, map_one]
    ring
  rw [h, mul_pow]

theorem connectionV_simple_root (n : ℕ) (hn : 1 ≤ n) :
    connectionV n - C (n : ℚ) = (X - C (1 : ℚ)) * (X + C (n : ℚ)) := by
  unfold connectionV
  rw [Nat.cast_sub hn]
  simp only [Nat.cast_one, map_sub, map_one]
  ring

theorem rootMultiplicity_le_natDegree_rat (q : ℚ[X]) (hq : q ≠ 0) (a : ℚ) :
    q.rootMultiplicity a ≤ q.natDegree := by
  have h := natDegree_le_of_dvd (pow_rootMultiplicity_dvd q a) hq
  simpa using h

theorem rootMultiplicity_simple_composition (q f g : ℚ[X]) (a b : ℚ)
    (hq : q ≠ 0) (hf : f - C a = (X - C b) * g)
    (hg : g.eval b ≠ 0) :
    (q.comp f).rootMultiplicity b = q.rootMultiplicity a := by
  obtain ⟨r, hr, hrdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd q hq a
  have hrval : r.eval a ≠ 0 := by
    simpa only [dvd_iff_isRoot, IsRoot.def] using hrdvd
  have hfa : f.eval b = a := by
    have hh := congrArg (fun p : ℚ[X] => p.eval b) hf
    simp only [eval_sub, eval_C, eval_mul, eval_X, sub_self, zero_mul] at hh
    exact sub_eq_zero.mp hh
  let m := q.rootMultiplicity a
  let s := g ^ m * r.comp f
  have hsval : s.eval b ≠ 0 := by
    dsimp [s]
    simp only [eval_mul, eval_pow, eval_comp, hfa]
    exact mul_ne_zero (pow_ne_zero _ hg) hrval
  have hs : s ≠ 0 := by
    intro h
    apply hsval
    simp [h]
  have hqs : q.comp f = s * (X - C b) ^ m := by
    rw [hr, mul_comp, pow_comp, sub_comp, X_comp, C_comp, hf]
    dsimp [s]
    rw [mul_pow]
    ring
  rw [hqs, rootMultiplicity_mul_X_sub_C_pow hs,
    rootMultiplicity_eq_zero (show ¬ IsRoot s b from hsval), zero_add]

theorem first_factor_eval_one_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    ((X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10).eval 1 ≠ 0 := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
  apply mul_ne_zero
  · linarith
  · apply pow_ne_zero
    linarith

theorem connection_homogeneous_q_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) : q = 0 := by
  by_contra hq
  let A : ℚ[X] := (X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10
  have hA : A.eval 1 ≠ 0 := first_factor_eval_one_ne_zero n hn
  have hA0 : A ≠ 0 := by
    intro h
    apply hA
    simp [h]
  have hcomp : q.comp (connectionV n) ≠ 0 := by
    intro h
    rcases comp_eq_zero_iff.mp h with h | ⟨_, hv⟩
    · exact hq h
    · have hv2 := congrArg (fun p : ℚ[X] => p.coeff 2) hv
      simp [connectionV, coeff_X_mul] at hv2
  have hF0 : A * q.comp (connectionV n) ≠ 0 := mul_ne_zero hA0 hcomp
  have hdvd : (X - C (1 : ℚ)) ^ 10 ∣ A * q.comp (connectionV n) := by
    refine ⟨(X + C (2 * (n : ℚ) + 1)) *
      q.comp ((X + 1) * (X + C (n : ℚ))) -
        (X + C ((n : ℚ) + 1)) ^ 10 * P.comp (connectionU n), ?_⟩
    rw [connectionD_factor] at heq
    dsimp [connectionH] at heq
    dsimp [A]
    simp only [map_one] at heq ⊢
    linear_combination heq
  have hmult : (A * q.comp (connectionV n)).rootMultiplicity 1 = q.rootMultiplicity (n : ℚ) := by
    rw [rootMultiplicity_mul hF0,
      rootMultiplicity_eq_zero (show ¬ IsRoot A 1 from hA), zero_add]
    apply rootMultiplicity_simple_composition q (connectionV n) (X + C (n : ℚ))
      (n : ℚ) 1 hq (connectionV_simple_root n hn)
    simp only [eval_add, eval_X, eval_C]
    positivity
  have hm10 := (le_rootMultiplicity_iff hF0).mpr hdvd
  rw [hmult] at hm10
  have hm9 := (rootMultiplicity_le_natDegree_rat q hq (n : ℚ)).trans hqdeg
  omega

theorem connectionU_comp_eq_zero (n : ℕ) (P : ℚ[X])
    (h : P.comp (connectionU n) = 0) : P = 0 := by
  rcases comp_eq_zero_iff.mp h with h | ⟨_, hu⟩
  · exact h
  · have h2 := congrArg (fun p : ℚ[X] => p.coeff 2) hu
    simp [connectionU, coeff_X_mul] at h2

theorem connection_homogeneous_kernel_zero (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hqdeg : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := by
  have hq := connection_homogeneous_q_zero n hn P q hqdeg heq
  have hD : connectionD n ≠ 0 := by
    rw [connectionD_factor]
    apply mul_ne_zero
    · exact pow_ne_zero _ (X_sub_C_ne_zero 1)
    · apply pow_ne_zero
      simpa only [sub_neg_eq_add, map_neg] using X_sub_C_ne_zero (-((n : ℚ) + 1))
  have hP : P.comp (connectionU n) = 0 := by
    simpa only [hq, connectionH, zero_comp, mul_zero, sub_self, add_zero,
      mul_eq_zero, hD, false_or] using heq
  exact ⟨connectionU_comp_eq_zero n P hP, hq⟩

def connectionReflection (n : ℕ) : ℚ[X] := -X - C (n : ℚ)

theorem connectionU_reflection (n : ℕ) :
    (connectionU n).comp (connectionReflection n) = connectionU n := by
  simp only [connectionU, connectionReflection, mul_comp, add_comp, X_comp, C_comp]
  ring

theorem connectionH_reflection (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]) :
    (connectionH n q).comp (connectionReflection n) = connectionH n q := by
  have hv : (connectionV n).comp (connectionReflection n) =
      (X + 1) * (X + C (n : ℚ)) := by
    simp only [connectionV, connectionReflection, mul_comp, add_comp, X_comp, C_comp]
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, map_sub, map_one]
    ring
  have hw : ((X + 1) * (X + C (n : ℚ))).comp (connectionReflection n) =
      connectionV n := by
    simp only [connectionV, connectionReflection, mul_comp, add_comp, X_comp, C_comp,
      one_comp]
    rw [Nat.cast_sub hn]
    simp only [Nat.cast_one, map_sub, map_one]
    ring
  have ha : (X - C ((n : ℚ) + 1)).comp (connectionReflection n) =
      -(X + C (2 * (n : ℚ) + 1)) := by
    rw [sub_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_mul, map_ofNat, map_one]
    ring
  have hb : (X + C ((n : ℚ) + 1)).comp (connectionReflection n) = -(X - 1) := by
    rw [add_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_one]
    ring
  have hc : (X + C (2 * (n : ℚ) + 1)).comp (connectionReflection n) =
      -(X - C ((n : ℚ) + 1)) := by
    rw [add_comp, X_comp, C_comp]
    simp only [connectionReflection, map_add, map_mul, map_ofNat, map_one]
    ring
  have hd : (X - 1 : ℚ[X]).comp (connectionReflection n) =
      -(X + C ((n : ℚ) + 1)) := by
    simp only [sub_comp, X_comp, one_comp, connectionReflection, map_add, map_one]
    ring
  simp only [connectionH, sub_comp, mul_comp, pow_comp, comp_assoc,
    hv, hw, ha, hb, hc, hd]
  ring

theorem reflected_natDegree_even (n : ℕ) (p : ℚ[X]) (hp : p ≠ 0)
    (href : p.comp (connectionReflection n) = p) : Even p.natDegree := by
  have hd : (connectionReflection n).natDegree = 1 := by
    rw [connectionReflection, natDegree_sub_C, natDegree_neg, natDegree_X]
  have hl : (connectionReflection n).leadingCoeff = -1 := by
    have heq : connectionReflection n = -(X + C (n : ℚ)) := by
      unfold connectionReflection
      ring
    rw [heq, leadingCoeff_neg, leadingCoeff_X_add_C]
  have hh := congrArg Polynomial.leadingCoeff href
  rw [leadingCoeff_comp (by omega), hl] at hh
  have hpow : (-1 : ℚ) ^ p.natDegree = 1 := by
    apply (mul_left_cancel₀ (leadingCoeff_ne_zero.mpr hp))
    simpa using hh
  exact (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℚ) ≠ 1)).mp hpow

theorem reflected_even_coefficients_determine (n : ℕ) (p : ℚ[X])
    (hdeg : p.natDegree ≤ 29) (href : p.comp (connectionReflection n) = p)
    (heven : ∀ i : Fin 15, p.coeff (2 * i.val) = 0) : p = 0 := by
  by_contra hp
  obtain ⟨k, hk⟩ := reflected_natDegree_even n p hp href
  have hk15 : k < 15 := by omega
  have h := heven ⟨k, hk15⟩
  have h2 : p.natDegree = 2 * k := by omega
  rw [← h2, coeff_natDegree] at h
  exact leadingCoeff_ne_zero.mpr hp h

def coefficientPolynomial (d : ℕ) (c : Fin d → ℚ) : ℚ[X] :=
  ∑ i : Fin d, c i • (X ^ i.val)

theorem coefficientPolynomial_coeff (d : ℕ) (c : Fin d → ℚ) (i : Fin d) :
    (coefficientPolynomial d c).coeff i.val = c i := by
  classical
  rw [coefficientPolynomial, finsetSum_coeff]
  simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero]
  apply Finset.sum_eq_single i
  · simp
  · intro j _ hji
    have hne : i.val ≠ j.val := by
      intro h
      exact hji (Fin.ext h.symm)
    simp [hne]
  · simp

theorem coefficientPolynomial_add (d : ℕ) (c e : Fin d → ℚ) :
    coefficientPolynomial d (c + e) = coefficientPolynomial d c + coefficientPolynomial d e := by
  classical
  simp only [coefficientPolynomial, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem coefficientPolynomial_smul (d : ℕ) (a : ℚ) (c : Fin d → ℚ) :
    coefficientPolynomial d (a • c) = a • coefficientPolynomial d c := by
  classical
  simp only [coefficientPolynomial, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem coefficientPolynomial_degree (d : ℕ) (c : Fin d → ℚ) :
    (coefficientPolynomial d c).natDegree ≤ d - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply (natDegree_smul_le (c i) (X ^ i.val)).trans
  simp only [natDegree_X_pow]
  omega

def inputP (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 5 (fun i => c ⟨i.val, by omega⟩)

def inputQ (c : Fin 15 → ℚ) : ℚ[X] :=
  coefficientPolynomial 10 (fun i => c ⟨i.val + 5, by omega⟩)

def connectionOperator (n : ℕ) (P q : ℚ[X]) : ℚ[X] :=
  connectionD n * P.comp (connectionU n) + connectionH n q

theorem connectionOperator_reflection (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X]) :
    (connectionOperator n P q).comp (connectionReflection n) = connectionOperator n P q := by
  simp only [connectionOperator, add_comp, mul_comp, connectionD, pow_comp,
    sub_comp, C_comp, connectionU_reflection, comp_assoc, connectionH_reflection n hn]

theorem connectionOperator_degree (n : ℕ) (P q : ℚ[X])
    (hP : P.natDegree ≤ 4) (hq : q.natDegree ≤ 9) :
    (connectionOperator n P q).natDegree ≤ 29 := by
  have hu : (connectionU n).natDegree ≤ 2 := by
    simpa only [connectionU, natDegree_X, natDegree_X_add_C] using (natDegree_mul_le (p := (X : ℚ[X]))
      (q := X + C (n : ℚ)))
  have hv : (connectionV n).natDegree ≤ 2 := by
    simpa only [connectionV, natDegree_X, natDegree_X_add_C] using (natDegree_mul_le (p := (X : ℚ[X]))
      (q := X + C ((n - 1 : ℕ) : ℚ)))
  have hw : (((X : ℚ[X]) + 1) * (X + C (n : ℚ))).natDegree ≤ 2 := by
    simpa only [← C_1, natDegree_X_add_C] using
      (natDegree_mul_le (p := (X : ℚ[X]) + C 1) (q := X + C (n : ℚ)))
  have hD : (connectionD n).natDegree ≤ 20 := by
    exact (natDegree_pow_le (p := connectionU n - C ((n : ℚ) + 1)) (n := 10)).trans
      (by simpa only [natDegree_sub_C] using Nat.mul_le_mul_left 10 hu)
  have hA : ((X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10).natDegree ≤ 11 := by
    simpa only [natDegree_X_sub_C, natDegree_pow, natDegree_X_add_C] using (natDegree_mul_le (p := (X : ℚ[X]) - C ((n : ℚ) + 1))
      (q := (X + C ((n : ℚ) + 1)) ^ 10))
  have hB : ((X + C (2 * (n : ℚ) + 1)) * (X - 1) ^ 10).natDegree ≤ 11 := by
    simpa only [← C_1, natDegree_X_add_C, natDegree_pow, natDegree_X_sub_C] using
      (natDegree_mul_le (p := (X : ℚ[X]) + C (2 * (n : ℚ) + 1))
      (q := (X - C 1) ^ 10))
  have hpcomp : (P.comp (connectionU n)).natDegree ≤ 8 :=
    natDegree_comp_le.trans (by nlinarith)
  have hqcomp : (q.comp (connectionV n)).natDegree ≤ 18 :=
    natDegree_comp_le.trans (by nlinarith)
  have hqwcomp : (q.comp ((X + 1) * (X + C (n : ℚ)))).natDegree ≤ 18 :=
    natDegree_comp_le.trans (by nlinarith)
  change (connectionD n * P.comp (connectionU n) + connectionH n q).natDegree ≤ 29
  apply natDegree_add_le_of_degree_le
  · exact natDegree_mul_le.trans (by omega)
  · unfold connectionH
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by omega)
    · exact natDegree_mul_le.trans (by omega)

theorem connectionOperator_add (n : ℕ) (P Q q r : ℚ[X]) :
    connectionOperator n (P + Q) (q + r) =
      connectionOperator n P q + connectionOperator n Q r := by
  simp only [connectionOperator, connectionH, add_comp, mul_add]
  ring

theorem connectionOperator_smul (n : ℕ) (a : ℚ) (P q : ℚ[X]) :
    connectionOperator n (a • P) (a • q) = a • connectionOperator n P q := by
  simp only [connectionOperator, connectionH, smul_comp, mul_smul_comm, smul_sub, smul_add]

def connectionLinearMap (n : ℕ) : (Fin 15 → ℚ) →ₗ[ℚ] (Fin 15 → ℚ) where
  toFun c i := (connectionOperator n (inputP c) (inputQ c)).coeff (2 * i.val)
  map_add' c d := by
    classical
    funext i
    have hP : inputP (c + d) = inputP c + inputP d :=
      coefficientPolynomial_add 5 _ _
    have hQ : inputQ (c + d) = inputQ c + inputQ d :=
      coefficientPolynomial_add 10 _ _
    simp only [hP, hQ, connectionOperator_add, coeff_add, Pi.add_apply]
  map_smul' a c := by
    classical
    funext i
    have hP : inputP (a • c) = a • inputP c := coefficientPolynomial_smul 5 a _
    have hQ : inputQ (a • c) = a • inputQ c := coefficientPolynomial_smul 10 a _
    simp only [hP, hQ, connectionOperator_smul, coeff_smul, Pi.smul_apply]

theorem connectionLinearMap_injective (n : ℕ) (hn : 1 ≤ n) :
    Function.Injective (connectionLinearMap n) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have hP : (inputP c).natDegree ≤ 4 := coefficientPolynomial_degree 5 _
  have hq : (inputQ c).natDegree ≤ 9 := coefficientPolynomial_degree 10 _
  have heven : ∀ i : Fin 15, (connectionOperator n (inputP c) (inputQ c)).coeff
      (2 * i.val) = 0 := by
    intro i
    exact congrFun hc i
  have hz := reflected_even_coefficients_determine n
    (connectionOperator n (inputP c) (inputQ c))
    (connectionOperator_degree n _ _ hP hq)
    (connectionOperator_reflection n hn _ _) heven
  obtain ⟨hP0, hq0⟩ := connection_homogeneous_kernel_zero n hn _ _ hq hz
  funext i
  by_cases hi : i.val < 5
  · have h := coefficientPolynomial_coeff 5 (fun j => c ⟨j.val, by omega⟩) ⟨i.val, hi⟩
    change (inputP c).coeff i.val = c i at h
    simpa only [hP0, coeff_zero] using h.symm
  · have h := coefficientPolynomial_coeff 10 (fun j => c ⟨j.val + 5, by omega⟩)
      ⟨i.val - 5, by omega⟩
    have hidx : i.val - 5 + 5 = i.val := by omega
    simpa only [← inputQ, hq0, coeff_zero, hidx] using h.symm

theorem connectionLinearMap_bijective (n : ℕ) (hn : 1 ≤ n) :
    Function.Bijective (connectionLinearMap n) :=
  ⟨connectionLinearMap_injective n hn,
    LinearMap.injective_iff_surjective.mp (connectionLinearMap_injective n hn)⟩

end ZetaNine.CoefficientMapConnection
