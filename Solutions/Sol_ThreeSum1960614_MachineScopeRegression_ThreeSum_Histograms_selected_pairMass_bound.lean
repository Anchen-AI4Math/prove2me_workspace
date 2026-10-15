import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Balancing
import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Finset
end Finset
namespace ThreeSum.Balancing
end ThreeSum.Balancing
namespace ThreeSum.Histograms
end ThreeSum.Histograms
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms

namespace ThreeSum1960614.MachineScopeRegression

/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing

open _root_.Finset
open scoped _root_.BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]



theorem sum_correlation (F H : G → ℕ) :
    (∑ d, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.sum_correlation] at hs
  exact (lt_irrefl _ hs)



theorem chooseOffset_le [Inhabited G] (keys : List G) (F H : G → ℕ)
    {d : G} (hd : d ∈ keys) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset keys F H) ≤ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H d := by
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset
  cases h : keys.argmin (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H) with
  | none => have := List.argmin_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmin (f := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H) hd
      (by simpa only [Option.mem_def] using h)

theorem chooseOffset_balanced [Inhabited G] (keys : List G) (hall : ∀ d, d ∈ keys)
    (F H : G → ℕ) :
    Fintype.card G * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation F H (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset keys F H) ≤
      (∑ k, F k) * (∑ k, H k) := by
  obtain ⟨d, hd⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.exists_balanced_offset F H
  exact (Nat.mul_le_mul_left _ (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset_le keys F H (hall d))).trans hd

end ThreeSum.Balancing

end ThreeSum1960614.MachineScopeRegression

namespace ThreeSum1960614.MachineScopeRegression

/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open _root_.Finset
open scoped _root_.BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]



theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp



theorem correlation_histograms (I : Finset ι) (J : Finset τ)
    (left : ι → G) (right : τ → G) (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram J right weightR) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram I left weightL) d =
      _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.pairMass I J left right weightL weightR d := by
  unfold _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.correlation _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.pairMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  have hinner (i : ι) :
      (∑ k : G, (if right j = k then weightR j else 0) *
        (if left i = k - d then weightL i else 0)) =
      if right j - left i = d then weightL i * weightR j else 0 := by
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    by_cases h : right j - left i = d
    · have h' : left i = right j - d := by exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
      simp [h, h', Nat.mul_comm]
    · have h' : left i ≠ right j - d := by
        intro h'
        apply h
        rw [h']
        abel
      simp [h, h']
  simp_rw [hinner]









end ThreeSum.Histograms

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms

open _root_.Finset
open scoped _root_.BigOperators
variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
/-- The actual raw-incidence/output-key join obeys the exact balancing bound
for the selected offset, without an independent hash-uniformity premise. -/
theorem solution [Inhabited G]
    (keys : List G) (hkeys : ∀ d, d ∈ keys)
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) :
    Fintype.card G * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.pairMass I J left right weightL weightR
      (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset keys (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram J right weightR) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram I left weightL)) ≤
        (∑ i ∈ I, weightL i) * (∑ j ∈ J, weightR j) := by
  have h := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Balancing.chooseOffset_balanced keys hkeys
    (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram J right weightR) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.histogram I left weightL)
  rw [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.correlation_histograms, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.sum_histogram, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Histograms.sum_histogram] at h
  simpa only [Nat.mul_comm] using h

#print axioms solution
