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



theorem OAI.PiExponent.exists_rational_parameters (ν : ℝ) (hν : 2 < ν) :
    ∃ θ A B C : ℚ,
      0 < (θ : ℝ) ∧ (θ : ℝ) < A ∧ (A : ℝ) < B ∧ (B : ℝ) < 1 ∧
      ν * ((A : ℝ) - θ) > 1 - θ ∧
      1 < (C : ℝ) ∧ (B : ℝ) < 1 / C ∧
      (B : ℝ) < C * θ ∧ (C : ℝ) * θ < 1 := by sorry
