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





/-- An explicitly enumerable parameter space: two coordinates and an 81-entry
choice of a color map. -/
abbrev Parameter (d : ℕ) := (Fin d × Fin d) × ((Bool × Bool) → Fin 3)

def applyColor {d : ℕ} (p : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.Parameter d) (word : Fin d → Bool) : Fin 3 :=
  p.2 (word p.1.1, word p.1.2)





/-- The minimum binary width needed for indices from zero through `n-1`. -/
def indexWidth (n : ℕ) : ℕ := Nat.size (n - 1)

def indexWord {n : ℕ} (i : Fin n) : Fin (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n) → Bool :=
  fun j => i.val.testBit j.val









def colorIndex {n : ℕ} (p : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.Parameter (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n)) (i : Fin n) : Fin 3 :=
  _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.applyColor p (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWord i)

/-- The actual family is an image of the small, explicitly enumerable
parameter domain. Duplicate colorings can be discarded. -/
def family (n : ℕ) : Finset (Fin n → Fin 3) :=
  Finset.univ.image (fun p : _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.Parameter (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.indexWidth n) => _root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.colorIndex p)









/-- Values are deduplicated inside each class, retaining original index
witnesses through image membership. -/
def values {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) (color : Fin 3) :
    Finset ℤ :=
  (Finset.univ.filter (fun i => c i = color)).image x

def negValues {n : ℕ} (x : Fin n → ℤ) (c : Fin n → Fin 3) : Finset ℤ :=
  (_root_.ThreeSum1960614.MachineScopeRegression.ThreeSum.Coloring.values x c 2).image (fun z => -z)





def DistinctZeroSum {n : ℕ} (x : Fin n → ℤ) : Prop :=
  ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ x i + x j + x k = 0

def ThreeSetWitness (a b c : Finset ℤ) : Prop :=
  ∃ u ∈ a, ∃ v ∈ b, ∃ w ∈ c, u + v = w







end ThreeSum.Coloring

end ThreeSum1960614.MachineScopeRegression
