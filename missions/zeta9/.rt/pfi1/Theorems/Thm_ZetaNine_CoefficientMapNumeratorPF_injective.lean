import Definitions.Def_ZetaNine_CoefficientMapNumeratorPF

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial ZetaNine ZetaNine.CoefficientMapNumeratorPartialFractions ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions

theorem ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective (m : ℕ) (A B : ℚ[X])
    (hA : A.natDegree < 9 * (m + 1)) (hB : B.natDegree < 9 * (m + 1))
    (heq : ∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) : A = B:= by sorry
