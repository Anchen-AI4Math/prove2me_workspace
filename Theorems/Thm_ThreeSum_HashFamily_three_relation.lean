import Definitions.Def_ThreeSum1962Source_Bundle01
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

universe u_1 u_2

theorem ThreeSum.HashFamily.three_relation : ∀ {α : Type u_1} {K : Type u_2} [inst : Ring.{u_2} K] {s t u : α → Bool} (hst : @Ne.{u_1 + 1} (α → Bool) s t)
  (hsu : @Ne.{u_1 + 1} (α → Bool) s u) (htu : @Ne.{u_1 + 1} (α → Bool) t u) {a b c : K}
  (h :
    ∀ (p : Prod.{u_1, 0} α Bool),
      @Eq.{u_2 + 1} K
        (@HAdd.hAdd.{u_2, u_2, u_2} K K K
          (@instHAdd.{u_2} K (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
          (@HAdd.hAdd.{u_2, u_2, u_2} K K K
            (@instHAdd.{u_2} K
              (@Distrib.toAdd.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
            (@HMul.hMul.{u_2, u_2, u_2} K K K
              (@instHMul.{u_2} K
                (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
              a
              (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                (@AddMonoidWithOne.toOne.{u_2} K
                  (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                s p))
            (@HMul.hMul.{u_2, u_2, u_2} K K K
              (@instHMul.{u_2} K
                (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
              b
              (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
                (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
                (@AddMonoidWithOne.toOne.{u_2} K
                  (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
                t p)))
          (@HMul.hMul.{u_2, u_2, u_2} K K K
            (@instHMul.{u_2} K
              (@Distrib.toMul.{u_2} K (@instDistribOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))
            c
            (@ThreeSum.HashFamily.oneHot.{u_1, u_2} α K
              (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))
              (@AddMonoidWithOne.toOne.{u_2} K
                (@AddGroupWithOne.toAddMonoidWithOne.{u_2} K (@Ring.toAddGroupWithOne.{u_2} K inst)))
              u p)))
        (@OfNat.ofNat.{u_2} K (nat_lit 0)
          (@Zero.toOfNat0.{u_2} K
            (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst)))))),
  And
    (@Eq.{u_2 + 1} K a
      (@OfNat.ofNat.{u_2} K (nat_lit 0)
        (@Zero.toOfNat0.{u_2} K
          (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
    (And
      (@Eq.{u_2 + 1} K b
        (@OfNat.ofNat.{u_2} K (nat_lit 0)
          (@Zero.toOfNat0.{u_2} K
            (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))
      (@Eq.{u_2 + 1} K c
        (@OfNat.ofNat.{u_2} K (nat_lit 0)
          (@Zero.toOfNat0.{u_2} K
            (@MulZeroClass.toZero.{u_2} K (@instMulZeroClassOfSemiring.{u_2} K (@Ring.toSemiring.{u_2} K inst))))))) := by
  sorry

