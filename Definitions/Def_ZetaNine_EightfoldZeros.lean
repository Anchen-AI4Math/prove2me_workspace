import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
The explicit eightfold-zero repair from `new-linear-form-route-repair-2026-10-02.md`.
The numerator has an eighth-power factor at each positive endpoint `1,...,n`.
Its derivatives through order seven vanish there, as do the genuine iterated
real derivatives of the rational function, whose denominator is nonzero there.
This file makes no sign, nonvanishing, asymptotic or irrationality claim.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace ZetaNine.EightfoldZeros

/-! ## Construction definitions (the lightweight Definitions layer) -/

/-- The exact scalar prefactor of the repair candidate. -/
def repairScale (n : ℕ) : ℝ :=
  ((Nat.factorial (4 * n) : ℝ) ^ 2) / ((Nat.factorial n : ℝ) ^ 8)

/-- The explicit repair numerator, with one eighth-power factor per endpoint. -/
def repairNumerator (n : ℕ) : ℝ[X] :=
  C (repairScale n) * ∏ j ∈ Finset.range n, (X - C ((j + 1 : ℕ) : ℝ)) ^ 8

/-- Its denominator is exactly `[t(t+1)...(t+4n)]²`. -/
def repairDenominator (n : ℕ) : ℝ[X] :=
  ∏ j ∈ Finset.range (4 * n + 1), (X + C (j : ℝ)) ^ 2

/-- The real rational function `R*_n` in the repair note. -/
def repairFunction (n : ℕ) (t : ℝ) : ℝ :=
  (repairNumerator n).eval t / (repairDenominator n).eval t


end ZetaNine.EightfoldZeros
