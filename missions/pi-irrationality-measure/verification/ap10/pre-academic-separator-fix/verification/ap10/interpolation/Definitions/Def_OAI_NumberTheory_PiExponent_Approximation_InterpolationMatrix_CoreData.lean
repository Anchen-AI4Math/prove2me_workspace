import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_InterpolationMatrix_Domains
import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_SimplexCounting_WeightedDomains

namespace OAI.PiExponent.InterpolationMatrix

open scoped BigOperators

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

end OAI.PiExponent.InterpolationMatrix
