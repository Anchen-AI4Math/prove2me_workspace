import Definitions.Def_ZetaNine_CoefficientMapJet

set_option autoImplicit false
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet

theorem ZetaNine.CoefficientMapJet.integer_coefficient_convolution (n j s : ℕ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) :
    weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, localCoefficient n j l *
        ((W.comp (integerLocalU n j)).coeff (l - s) : ℚ):= by sorry
