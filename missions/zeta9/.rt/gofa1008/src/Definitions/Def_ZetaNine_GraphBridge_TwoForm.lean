import Definitions.Def_ZetaNine_CoefficientMapMatrix
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Finset Polynomial Filter

namespace ZetaNine.GraphBridge
open CoefficientMapMatrix

/-- Weighted size of the genuine inverse row (b,a) S F_n inverse. -/
def selectedInverseWeightedNorm (n : ℕ) (b a : ℤ) : ℝ :=
  ∑ i : Fin 5,
    |((selectedIntegerPair b a ᵥ* (selectionMatrix * (actualFMatrix n)⁻¹)) i : ℝ)| *
      (n : ℝ) ^ (2 * i.val)

/-- Geometric short-vector obligation, on unbounded even scales.
This does not assume the value of any zeta linear form is small. -/
def SelectedInverseShortPairMargin : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N : ℕ, ∃ k : ℕ, N ≤ k ∧ 2 ≤ k ∧ Even k ∧
      ∃ b₁ a₁ b₂ a₂ : ℤ,
        b₁ * a₂ ≠ b₂ * a₁ ∧
        selectedInverseWeightedNorm k b₁ a₁ ≤
          Real.exp (((2641 / 250 : ℝ) - δ) * k) ∧
        selectedInverseWeightedNorm k b₂ a₂ ≤
          Real.exp (((2641 / 250 : ℝ) - δ) * k)

end ZetaNine.GraphBridge
