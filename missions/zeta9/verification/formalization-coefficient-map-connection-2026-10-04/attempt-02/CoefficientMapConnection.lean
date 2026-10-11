import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
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

end ZetaNine.CoefficientMapConnection
