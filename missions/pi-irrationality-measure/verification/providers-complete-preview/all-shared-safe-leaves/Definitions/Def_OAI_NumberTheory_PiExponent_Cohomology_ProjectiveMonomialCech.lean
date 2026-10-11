import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Finsupp.Basic




namespace OAI

namespace PiExponent.ProjectiveMonomialCech

noncomputable section

open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [AddCommGroup K]

def Monomial (ι : Type*) [Fintype ι] (d : ℤ) :=
  {a : ι → ℤ // ∑ i, a i = d}

abbrev Laurent (ι K : Type*) [Fintype ι] [Zero K] (d : ℤ) :=
  Monomial ι d →₀ K

def RegularOn {d : ℤ} (s : Set ι) (f : Laurent ι K d) : Prop :=
  ∀ a, f a ≠ 0 → ∀ k, a.val k < 0 → k ∈ s















theorem exists_nonnegative_coordinate [Nonempty ι] {d : ℤ}
    (hd : 0 ≤ d) (a : Monomial ι d) : ∃ i, 0 ≤ a.val i := by
  by_contra h
  have hneg : ∀ i, a.val i < 0 := fun i => lt_of_not_ge (fun hi => h ⟨i, hi⟩)
  have htotal : (∑ i, a.val i) < 0 :=
    Finset.sum_neg (fun i _ => hneg i) Finset.univ_nonempty
  rw [a.property] at htotal
  exact (not_lt_of_ge hd) htotal



end
end PiExponent.ProjectiveMonomialCech

end OAI
