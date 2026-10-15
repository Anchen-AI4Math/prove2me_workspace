import Definitions.Def_ThreeSum1960614_MachineScopeRegression_Submission_ThreeSum_Coloring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_MachineScopeRegression_ThreeSum_Coloring_two_coordinates_separate

namespace ThreeSum.Coloring
end ThreeSum.Coloring
namespace ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring
end ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

namespace ThreeSum1960614.MachineScopeRegression

/-!
# A finite, deterministic three-color reduction

The family below enumerates two positions of the binary representation of an
array index and all 81 maps from their four patterns to three colors.  Its
parameter count is exactly `81 * d^2`.  In particular it never enumerates all
three-colorings of the input.  The final equivalence allows repeated input
values and deduplicates each color class into a finite set.
-/

namespace ThreeSum.Coloring

variable {α : Type*}











/-- Enumeration of the small parameter space separates the words in the
specified order, so no permutation of the three-set equation is needed. -/
theorem exists_separating_parameter {d : ℕ} {s t u : Fin d → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∃ p : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.Parameter d, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor p s = 0 ∧ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor p t = 1 ∧
      _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor p u = 2 := by
  obtain ⟨i, j, hst', hsu', htu'⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.two_coordinates_separate hst hsu htu
  let f : (Bool × Bool) → Fin 3 := fun x =>
    if x = (s i, s j) then 0 else if x = (t i, t j) then 1 else 2
  refine ⟨((i, j), f), ?_, ?_, ?_⟩
  · simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor, f]
  · simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor, f, Ne.symm hst']
  · simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor, f, Ne.symm hsu', Ne.symm htu']





theorem index_lt_pow_width {n : ℕ} (i : Fin n) : i.val < 2 ^ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n := by
  exact (show i.val ≤ n - 1 by omega).trans_lt (Nat.lt_size_self (n - 1))

theorem indexWord_injective (n : ℕ) : Function.Injective (@_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWord n) := by
  intro i j hij
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n
  · exact congrFun hij ⟨k, hk⟩
  · have hp : 2 ^ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt ((_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.index_lt_pow_width i).trans_le hp),
      Nat.testBit_eq_false_of_lt ((_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.index_lt_pow_width j).trans_le hp)]















theorem family_separates {n : ℕ} {i j k : Fin n}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ c ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.family n, c i = 0 ∧ c j = 1 ∧ c k = 2 := by
  obtain ⟨p, hp⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.exists_separating_parameter
    (fun h => hij (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWord_injective n h)) (fun h => hik (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWord_injective n h))
    (fun h => hjk (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWord_injective n h))
  exact ⟨_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.colorIndex p, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, hp⟩





theorem mem_values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3)
    (color : Fin 3) (v : ℤ) :
    v ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c color ↔ ∃ i, c i = color ∧ x i = v := by
  simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values]

theorem mem_negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (v : ℤ) :
    v ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.negValues x c ↔ ∃ i, c i = 2 ∧ -x i = v := by
  simp [_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.negValues, _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_values]











end ThreeSum.Coloring

end ThreeSum1960614.MachineScopeRegression

open _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring

variable {α : Type*}
/-- Exact equivalence between an array 3SUM witness at distinct positions and
one of the enumerated, deduplicated three-set instances. -/
theorem solution {n : ℕ} (x : Fin n → ℤ) :
    _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.DistinctZeroSum x ↔ ∃ c ∈ _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.family n,
      _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.ThreeSetWitness (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c 0) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c 1) (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.negValues x c) := by
  constructor
  · rintro ⟨i, j, k, hij, hik, hjk, hsum⟩
    obtain ⟨c, hc, hi, hj, hk⟩ := _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.family_separates hij hik hjk
    refine ⟨c, hc, x i, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_values x c 0 _).mpr ⟨i, hi, rfl⟩,
      x j, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_values x c 1 _).mpr ⟨j, hj, rfl⟩,
      -x k, (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_negValues x c _).mpr ⟨k, hk, rfl⟩, ?_⟩
    omega
  · rintro ⟨c, _, a, ha, b, hb, z, hz, he⟩
    obtain ⟨i, hi, rfl⟩ := (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_values x c 0 a).mp ha
    obtain ⟨j, hj, rfl⟩ := (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_values x c 1 b).mp hb
    obtain ⟨k, hk, rfl⟩ := (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.mem_negValues x c z).mp hz
    refine ⟨i, j, k, ?_, ?_, ?_, by omega⟩
    · intro heq
      subst j
      simp_all
    · intro heq
      subst k
      simp_all
    · intro heq
      subst k
      simp_all

#print axioms solution
