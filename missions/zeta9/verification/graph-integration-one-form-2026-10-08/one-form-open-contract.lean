import Definitions.Def_ZetaNine_CoefficientMapMatrix
import Mathlib

/-!
UNCOMPILED TYPE CONTRACT ONLY, prepared without Lean execution or API access.
This is the actual inverse-image and Taylor-cone construction obligation.
It keeps the notes' unbounded even scales, rather than eventual every even scale.
The sorry is an explicitly Open problem, never a claimed complete proof.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Polynomial Filter
open ZetaNine ZetaNine.CoefficientMapMatrix

namespace ZetaNine.GraphOneForm

theorem unbounded_short_positive_actual_selected_inverse :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ N : ℕ, ∃ (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b a : ℤ),
        N ≤ n ∧
        (∀ i : ℕ, 0 ≤
          (Polynomial.taylor (((n : ℝ) + 1) * (2 * (n : ℝ) + 1))
            ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ))).coeff i) ∧
        0 < ((selectedIntegerMultiplier n hn2 hn b a).map (Rat.castHom ℝ)).eval
          (((n : ℝ) + 2) * ((n : ℝ) + 2 + (n : ℝ))) ∧
        (∑ r ∈ Finset.range 5,
          |((selectedIntegerMultiplier n hn2 hn b a).coeff r : ℝ)| *
            (n : ℝ) ^ (2 * r)) ≤
          Real.exp (((2641 / 250 : ℝ) - δ) * (n : ℝ)) := by sorry

end ZetaNine.GraphOneForm
