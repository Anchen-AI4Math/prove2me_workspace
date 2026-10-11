import Definitions.Def_ZetaNine_CoefficientMapJet
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity

def baseNumerator (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))

def baseU (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))

def weightedNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] := baseNumerator n * W.comp (baseU n)

def polePolynomial (n : ℕ) : ℚ[X] := ∏ j ∈ range (n + 1), (X + C (j : ℚ))

def AllLocalCoefficientsZero (n : ℕ) (W : ℚ[X]) : Prop :=
  ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
    CoefficientMapJet.weightedLocalCoefficient n j s W = 0

def ProperMultiplier (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree < 9 * (n + 1)

def fullLocalCoefficientMap (n : ℕ) (W : ℚ[X]) : Fin (n + 1) → Fin 9 → ℚ :=
  fun j s => CoefficientMapJet.weightedLocalCoefficient n j.val (s.val + 1) W

end ZetaNine.CoefficientMapInjectivity
