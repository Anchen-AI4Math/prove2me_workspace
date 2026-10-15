import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_HashFamily
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_HashFamily_three_relation

namespace ThreeSum.HashFamily
end ThreeSum.HashFamily
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily
end ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

open scoped _root_.BigOperators
variable {α K : Type*}
open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily

variable [Ring K]
/-- If the equality masks of two edges differ, one coordinate has a 3+1
pattern among their four endpoint words. With four distinct endpoints this
forces full independence. The only possible no-shared-endpoint dependence
therefore has an identical output equality mask. -/
theorem solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) {a b c d : K}
    (h : ∀ p, a * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot s p + b * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot t p + c * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot u p + d * _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot v p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    obtain ⟨i, hi⟩ := hm
    have hf := h (i, false)
    have ht := h (i, true)
    cases hs : s i <;> cases hti : t i <;> cases hu : u i <;> cases hv : v i <;>
      simp_all [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.oneHot]
  rcases hz with ha | hb | hc | hd
  · have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation htu htv huv (a := b) (b := c) (c := d)
      (fun p => by simpa [ha] using h p)
    exact ⟨ha, hr.1, hr.2.1, hr.2.2⟩
  · have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation hsu hsv huv (a := a) (b := c) (c := d)
      (fun p => by simpa [hb] using h p)
    exact ⟨hr.1, hb, hr.2.1, hr.2.2⟩
  · have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation hst hsv htv (a := a) (b := b) (c := d)
      (fun p => by simpa [hc] using h p)
    exact ⟨hr.1, hr.2.1, hc, hr.2.2⟩
  · have hr := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.HashFamily.three_relation hst hsu htu (a := a) (b := b) (c := c)
      (fun p => by simpa [hd] using h p)
    exact ⟨hr.1, hr.2.1, hr.2.2, hd⟩

#print axioms solution
