import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Regular.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.Tactic.NormNum


namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def shiftHilbertPolynomial (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.X - Polynomial.C (d : ℚ))

@[simp] theorem shiftHilbertPolynomial_eval (p : Polynomial ℚ) (d n : ℕ)
    (hdn : d ≤ n) :
    (shiftHilbertPolynomial p d).eval (n : ℚ) = p.eval ((n-d : ℕ) : ℚ) := by
  simp [shiftHilbertPolynomial, Polynomial.eval_comp, Nat.cast_sub hdn]















end PiExponentJets.W64

end OAI
