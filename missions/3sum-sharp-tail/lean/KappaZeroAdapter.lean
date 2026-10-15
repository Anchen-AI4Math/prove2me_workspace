import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThreeSumSharpTail

/-- A uniform 3SUM bound for every positive input exponent also covers exponent zero. -/
theorem extend_to_kappa_zero (r : ℚ)
    (h : ∀ κ : ℕ, 1 ≤ κ →
      ∃ (P : List EndStatement.Instr) (b : ℕ) (T : ℕ → ℕ),
        EndStatement.BigO T r ∧
        ∀ (n : ℕ) (x : EndStatement.ThreeSum.Instance n),
          (∀ a ∈ EndStatement.ThreeSum.input x, a.natAbs ≤ n ^ κ) →
          ∀ W ≥ b * (Nat.log2 n + 1), EndStatement.ThreeSum.SolvedBy x P W (T n)) :
    EndStatement.ThreeSum.SolvedInTime r := by
  intro κ
  by_cases hκ : 1 ≤ κ
  · exact h κ hκ
  · have hκ0 : κ = 0 := by omega
    subst κ
    obtain ⟨P, b, T, hT, hsolve⟩ := h 1 le_rfl
    refine ⟨P, b, T, hT, fun n x hx W hW => hsolve n x ?_ W hW⟩
    intro a ha
    by_cases hn : n = 0
    · subst n
      change a ∈ List.ofFn (x : Fin 0 → ℤ) at ha
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp ha
      exact Fin.elim0 i
    · have hsize : 1 ≤ n := by omega
      have hsmall := hx a ha
      simp only [pow_zero] at hsmall
      simpa using hsmall.trans hsize

end ThreeSumSharpTail

#print axioms ThreeSumSharpTail.extend_to_kappa_zero
