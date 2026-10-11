import OAI.NumberTheory.PiExponent.Cohomology.EulerDifferencePolynomial

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open scoped BigOperators

-- The source Mathlib revision allows k ≤ n+d; the platform revision exposes
-- only the k ≤ n case. Keep the missing small-n case using its original proof.
private theorem preHilbertPoly_diagonal_eval (k n : ℕ) :
    (Polynomial.preHilbertPoly ℚ k k).eval (n : ℚ) = (n.choose k : ℚ) := by
  rcases le_or_gt k n with h | h
  · simpa only [Nat.sub_add_cancel h] using
      Polynomial.preHilbertPoly_eq_choose_sub_add ℚ k h
  · rw [Nat.choose_eq_zero_of_lt h]
    have hz : (ascPochhammer ℚ k).eval ((n : ℚ) - k + 1) = 0 := by
      apply (ascPochhammer_eval_eq_zero_iff _ _).mpr
      refine ⟨k - n - 1, by omega, ?_⟩
      rw [Nat.sub_sub, Nat.cast_sub (by omega : n + 1 ≤ k)]
      push_cast
      ring
    simp [Polynomial.preHilbertPoly, hz]

def newtonPolynomial (f : ℕ → ℤ) (d : ℕ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (d+1),
    Polynomial.C (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℚ) *
      Polynomial.preHilbertPoly ℚ k k

theorem newtonPolynomial_natDegree_le (f : ℕ → ℤ) (d : ℕ) :
    (newtonPolynomial f d).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_mul_le).trans
  simpa only [Polynomial.natDegree_C, Polynomial.natDegree_preHilbertPoly, zero_add] using
    (show k ≤ d by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk)

theorem newtonPolynomial_eval (f : ℕ → ℤ) (d : ℕ)
    (hzero : (fwdDiff (1 : ℕ))^[d+1] f = 0) (n : ℕ) :
    (newtonPolynomial f d).eval (n : ℚ) = (f n : ℚ) := by
  have h := integer_newton_sum_of_forwardDifference_eq_zero f d hzero n
  have hq : (f n : ℚ) = ∑ k ∈ Finset.range (d+1),
      (n.choose k : ℚ) * (((fwdDiff (1 : ℕ))^[k] f 0 : ℤ) : ℚ) := by
    exact_mod_cast h
  rw [hq]
  simp only [newtonPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  rw [preHilbertPoly_diagonal_eval]
  ring

end
end PiExponent.NumericalAmpleness

end OAI
