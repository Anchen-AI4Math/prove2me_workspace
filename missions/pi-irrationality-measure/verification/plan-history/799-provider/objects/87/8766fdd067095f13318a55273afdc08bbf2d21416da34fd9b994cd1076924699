import Mathlib.RingTheory.Algebraic.Basic

/- Minimal backport of the newer Mathlib interface used by family 017.
   This module remains inside the OAI import closure for graph extraction. -/
namespace Transcendental

theorem ne_zero {R A : Type*} [CommRing R] [Nontrivial R] [Ring A]
    [Algebra R A] {x : A} (hx : Transcendental R x) : x ≠ 0 := by
  intro h
  apply hx
  rw [h]
  exact isAlgebraic_zero

end Transcendental
