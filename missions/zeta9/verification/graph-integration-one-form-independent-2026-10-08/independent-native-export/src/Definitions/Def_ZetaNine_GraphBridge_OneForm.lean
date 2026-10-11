import Definitions.Def_ZetaNine_GraphBridge_TwoForm
import Mathlib.Algebra.Polynomial.Taylor

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
open Polynomial Filter

namespace ZetaNine.GraphBridge
open CoefficientMapMatrix

/-- The actual selected inverse polynomial lies in a positive Taylor cone
and meets the genuine inverse-coefficient size margin on unbounded even scales.
The positivity certificate is a finite polynomial evaluation, not a hypothesis
about the value or nonvanishing of the complete zeta linear form. -/
def SelectedInversePositiveConeMargin : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ∀ N : ℕ, ∃ (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ),
      N ≤ n ∧
      selectedInverseWeightedNorm n b a ≤
        Real.exp (((2641 / 250 : ℝ) - δ) * n) ∧
      (∀ i : ℕ, 0 ≤
        (Polynomial.taylor (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
          ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ))).coeff i) ∧
      0 < ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ)).eval
        (((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ)))

end ZetaNine.GraphBridge
