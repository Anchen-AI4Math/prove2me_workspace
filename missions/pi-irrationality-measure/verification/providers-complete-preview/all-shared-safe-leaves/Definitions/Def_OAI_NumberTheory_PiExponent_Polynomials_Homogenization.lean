import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.MvPolynomial.Homogeneous


namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators
open MvPolynomial

variable {k σ : Type*} [CommRing k]

noncomputable def dehomogenize : MvPolynomial (Option σ) k →+* MvPolynomial σ k :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun o : Option σ => o.elim 1 MvPolynomial.X)

@[simp] theorem dehomogenize_X_none :
    dehomogenize (MvPolynomial.X none : MvPolynomial (Option σ) k) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_rename (p : MvPolynomial σ k) :
    dehomogenize (MvPolynomial.rename some p) = p := by
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun o : Option σ => o.elim 1 MvPolynomial.X) (MvPolynomial.rename some p) = p
  rw [MvPolynomial.eval₂Hom_rename]
  change MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X p = p
  exact MvPolynomial.eval₂_eta p

noncomputable def homogenize (p : MvPolynomial σ k) : MvPolynomial (Option σ) k :=
  ∑ i ∈ Finset.range (p.totalDegree + 1),
    MvPolynomial.rename some (MvPolynomial.homogeneousComponent i p) *
      MvPolynomial.X none ^ (p.totalDegree - i)

@[simp] theorem dehomogenize_homogenize (p : MvPolynomial σ k) :
    dehomogenize (homogenize p) = p := by
  simp only [homogenize, map_sum, map_mul, map_pow, dehomogenize_rename,
    dehomogenize_X_none, one_pow, mul_one]
  exact MvPolynomial.sum_homogeneousComponent p

theorem homogenize_isHomogeneous (p : MvPolynomial σ k) :
    (homogenize p).IsHomogeneous p.totalDegree := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  have hi' : i ≤ p.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hcomponent :=
    (MvPolynomial.homogeneousComponent_isHomogeneous i p).rename_isHomogeneous
      (f := (some : σ → Option σ))
  simpa only [Nat.add_sub_of_le hi'] using
    hcomponent.mul (MvPolynomial.isHomogeneous_X_pow (none : Option σ) (p.totalDegree - i))







end PiExponentJets.W22

end OAI
