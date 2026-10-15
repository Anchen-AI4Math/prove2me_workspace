import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent

open Filter Topology

noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

noncomputable def strictWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (realWeightedSimplex w H).filter (fun a => ∑ i, w i * (a i : ℝ) < H)

end PiExponent

end OAI
