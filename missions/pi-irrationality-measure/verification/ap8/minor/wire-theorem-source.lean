import Mathlib

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

theorem exists_full_row_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by
  sorry

end PiExponent.InterpolationMatrix

end OAI
