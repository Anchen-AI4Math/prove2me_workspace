import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic



theorem OAI.PiExponent.exists_minimum_weight
    (m : ℕ) (hm : 1 ≤ m) (w : Fin m → ℝ) (X : ℝ)
    (hX : ∀ i, X < w i) :
    ∃ wstar : ℝ, X < wstar ∧ (∀ i, wstar ≤ w i) ∧
      ∃ i, wstar = w i := by sorry
