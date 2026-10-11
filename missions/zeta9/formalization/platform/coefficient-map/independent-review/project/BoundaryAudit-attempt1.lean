import Solutions.Sol_ZetaNine_CoefficientMap_weightedLeadingPoleCoefficient_eq_even
import Lean

set_option autoImplicit false
noncomputable section
open Finset Polynomial ZetaNine.CoefficientMap

namespace IndependentIntegration

theorem regular_statement (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    actualR n t * (t + j) ^ 9 = clearedR n j t := by
  exact clear_highest_pole n j hj t ht

theorem actual_denominator_nonzero (n j : ℕ) (hj : j ≤ n) :
    clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  exact clearedPoleProduct_ne_zero n j hj

theorem unweighted_statement (n j : ℕ) (hj : j ≤ n) :
    leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  exact leadingPoleCoefficient_eq n j hj

theorem weighted_statement (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  exact solution n j hn hj W

theorem unweighted_integer_nonzero (n j : ℕ) (hj : j ≤ n) :
    (∃ z : ℤ, leadingPoleCoefficient n j = (z : ℚ)) ∧
      leadingPoleCoefficient n j ≠ 0 := by
  exact ⟨leadingPoleCoefficient_is_integer n j hj,
    leadingPoleCoefficient_ne_zero n j hj⟩

theorem n_zero_boundary : leadingPoleCoefficient 0 0 = 1 := by
  simpa using leadingPoleCoefficient_eq 0 0 le_rfl

theorem arbitrary_zero_W (n j : ℕ) :
    weightedLeadingPoleCoefficient n j (0 : ℚ[X]) = 0 := by
  simp [weightedLeadingPoleCoefficient, clearedWeightedR]

theorem nonzero_W_can_cancel :
    (X + C 1 : ℚ[X]) ≠ 0 ∧
      weightedLeadingPoleCoefficient 2 1 (X + C 1 : ℚ[X]) = 0 := by
  constructor
  · intro h
    have hp := congrArg (fun p : ℚ[X] => p.coeff 1) h
    norm_num at hp
  · norm_num [weightedLeadingPoleCoefficient, clearedWeightedR]

end IndependentIntegration

open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let axioms ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty),
      ("axioms", toJson (axioms.toList.map Name.toString))]).compress
  emit `IndependentIntegration.regular_statement
  emit `IndependentIntegration.actual_denominator_nonzero
  emit `IndependentIntegration.unweighted_statement
  emit `IndependentIntegration.weighted_statement
  emit `IndependentIntegration.unweighted_integer_nonzero
  emit `IndependentIntegration.n_zero_boundary
  emit `IndependentIntegration.arbitrary_zero_W
  emit `IndependentIntegration.nonzero_W_can_cancel
