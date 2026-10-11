import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import missions.zeta9.formalization.CoefficientMapMatrix

/-!
OFFLINE ONLY: no Lean invocation has been made for this file.
The `...Statement` definitions are exact propositions proposed for the next
module. A proposition definition does not supply a proof or declare an axiom.
The five theorems at the start have written proof candidates, still uncompiled.
No existing frozen source is edited. See the adjacent exact-rational report.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapLocalTransportOffline

open CoefficientMapJet CoefficientMapInjectivity
open CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapNumeratorPartialFractions CoefficientMapFiniteSum
open CoefficientMapAggregate CoefficientMapMatrix

/-- Written proof candidate; not compiled. -/
theorem local_add_candidate (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A + B) =
      numeratorLocalCoefficient m j s A + numeratorLocalCoefficient m j s B := by
  simp only [numeratorLocalCoefficient, numeratorClearedSeries,
    Polynomial.add_comp, Polynomial.coe_add, add_mul, map_add]

/-- Written proof candidate; not compiled. -/
theorem local_smul_candidate (m j s : ℕ) (a : ℚ) (A : ℚ[X]) :
    numeratorLocalCoefficient m j s (a • A) =
      a * numeratorLocalCoefficient m j s A := by
  simp [numeratorLocalCoefficient, numeratorClearedSeries,
    Polynomial.smul_comp, smul_eq_mul]

/-- No degree bound: divisibility at the actual pole annihilates all nine jets. -/
theorem local_zero_of_shift_X_nine_candidate (m j s : ℕ) (A : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9)
    (hA : (X : ℚ[X]) ^ 9 ∣ A.comp (shiftedVariable j)) :
    numeratorLocalCoefficient m j s A = 0 := by
  obtain ⟨B, hB⟩ := hA
  have hseries : PowerSeries.X ^ 9 ∣ numeratorClearedSeries m j A := by
    refine ⟨(B : PowerSeries ℚ) *
      ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹, ?_⟩
    simp only [numeratorClearedSeries, hB, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X]
    ring
  exact PowerSeries.X_pow_dvd_iff.mp hseries (9 - s) (by omega)

/-- The right endpoint is present; both coefficient lists have equal lengths. -/
theorem finite_difference_total_candidate (N : ℕ) (c : ℕ → ℚ) :
    (∑ j ∈ range (N + 1), c j) - (∑ j ∈ range N, c j) = c N := by
  rw [Finset.sum_range_succ]
  ring

/-- Written bridge using the existing genuine PF endpoint; not compiled here. -/
theorem actual_remainder_PF_at_one_candidate (n : ℕ) (hn : 1 ≤ n)
    (q : ℚ[X]) (hq : q.natDegree ≤ 9) :
    (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
      remainderCoefficient n j s q / ((j : ℚ) + 1) ^ s) = 0 := by
  have hregular : ∀ k ≤ n + 1, (1 : ℚ) + (k : ℚ) ≠ 0 := by
    intro k hk
    exact ne_of_gt (by positivity)
  have hpf := actual_numerator_global_partial_fractions (n + 1)
    (shiftedRemainderNumerator n q)
    (shiftedRemainderNumerator_strict_proper n hn q hq) 1 hregular
  rw [shiftedRemainderNumerator_eval_one n hn q, zero_div] at hpf
  simpa only [remainderCoefficient, Nat.add_assoc, Nat.reduceAdd,
    add_comm (1 : ℚ)] using hpf.symm

/- The following are theorem CONTRACTS, not proved declarations. -/

def UpperClearedDenominatorStatement : Prop :=
  ∀ m j : ℕ, j ≤ m →
    shiftedClearedDenominator (m + 1) j =
      shiftedClearedDenominator m j * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ))

def LowerClearedDenominatorStatement : Prop :=
  ∀ m j : ℕ, 1 ≤ j → j ≤ m + 1 →
    shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * shiftedClearedDenominator m (j - 1)

def UpperActualSeriesStatement : Prop :=
  ∀ m j : ℕ, ∀ A : ℚ[X], j ≤ m →
    numeratorClearedSeries (m + 1) j ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      numeratorClearedSeries m j A

def LowerActualSeriesStatement : Prop :=
  ∀ m j : ℕ, ∀ A : ℚ[X], 1 ≤ j → j ≤ m + 1 →
    numeratorClearedSeries (m + 1) j (X ^ 9 * A.comp (X + 1)) =
      numeratorClearedSeries m (j - 1) A

def UpperActualJetStatement : Prop :=
  ∀ m j s : ℕ, ∀ A : ℚ[X], j ≤ m + 1 → 1 ≤ s → s ≤ 9 →
    numeratorLocalCoefficient (m + 1) j s
      ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
        if j ≤ m then numeratorLocalCoefficient m j s A else 0

def LowerActualJetStatement : Prop :=
  ∀ m j s : ℕ, ∀ A : ℚ[X], j ≤ m + 1 → 1 ≤ s → s ≤ 9 →
    numeratorLocalCoefficient (m + 1) j s (X ^ 9 * A.comp (X + 1)) =
      if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) s A

def DoubleActualJetStatement : Prop :=
  ∀ n j s : ℕ, ∀ A : ℚ[X], j ≤ n + 2 → 1 ≤ s → s ≤ 9 →
    numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
      if 1 ≤ j ∧ j ≤ n + 1 then numeratorLocalCoefficient n (j - 1) s A else 0

/-- Universal desired actual endpoint: no coefficient-array/PF hypothesis. -/
def ActualChosenLocalTransportStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5, ∀ j s : ℕ,
    j ≤ n + 2 → 1 ≤ s → s ≤ 9 →
    weightedLocalCoefficient (n + 2) j s (X ^ r.val) =
      extendedOldCoefficient n j s (connectionP n r) +
        extendedRemainderCoefficient n j s (connectionQ n r) -
          previousRemainderCoefficient n j s (connectionQ n r)

def ActualChosenLeftEndpointStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5, ∀ s : ℕ, 1 ≤ s → s ≤ 9 →
    weightedLocalCoefficient (n + 2) 0 s (X ^ r.val) =
      remainderCoefficient n 0 s (connectionQ n r)

def ActualChosenRightEndpointStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5, ∀ s : ℕ, 1 ≤ s → s ≤ 9 →
    weightedLocalCoefficient (n + 2) (n + 2) s (X ^ r.val) =
      -remainderCoefficient n (n + 1) s (connectionQ n r)

def ActualChosenAllRhoStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5, ∀ s : ℕ, 1 ≤ s → s ≤ 9 →
    CoefficientMapFiniteSum.rho (n + 2) s (X ^ r.val) =
      CoefficientMapFiniteSum.rho n s (connectionP n r)

/-- The finite harmonic algebra can precede either of the two PF evaluations. -/
def ActualChosenConstantCorrectionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5,
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r) -
      (∑ k ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n k s (connectionP n r) / ((k : ℚ) + 1) ^ s) +
      (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
        remainderCoefficient n j s (connectionQ n r) / ((j : ℚ) + 1) ^ s)

def ActualOldAtOneStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ P : ℚ[X], P.natDegree ≤ 4 →
    (∑ k ∈ range (n + 1), ∑ s ∈ Icc 1 9,
      weightedLocalCoefficient n k s P / ((k : ℚ) + 1) ^ s) = 0

/-- Uses genuine PF for Ahat, at x=1, not an assumed PF array. -/
def ActualRemainderPFAtOneStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ q : ℚ[X], q.natDegree ≤ 9 →
    (∑ j ∈ range (n + 2), ∑ s ∈ Icc 1 9,
      remainderCoefficient n j s q / ((j : ℚ) + 1) ^ s) = 0

def ActualChosenConstantStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5,
    constantTerm (n + 2) (X ^ r.val) = constantTerm n (connectionP n r)

def ActualChosenAggregateStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ r : Fin 5,
    aggregate (n + 2) (X ^ r.val) = aggregate n (connectionP n r)

/-- Matrix rows are multiplier monomials: Gamma multiplies on the left. -/
def ActualGammaMatrixStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → actualFMatrix (n + 2) = connectionGamma n * actualFMatrix n

/-- Paper row-coordinate action, valid independently of even-n invertibility. -/
def ActualGammaRowActionStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ v : Fin 5 → ℚ,
    v ᵥ* actualFMatrix (n + 2) = (v ᵥ* connectionGamma n) ᵥ* actualFMatrix n

end ZetaNine.CoefficientMapLocalTransportOffline
