import missions.zeta9.formalization.CoefficientMapJet
import Lean

open Lean Meta Polynomial
open scoped BigOperators
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false

-- This is the original even n>=2, integer-quartic regime. No coefficient
-- convolution, decomposition or inverse-matrix formula is assumed.
theorem checked_original_local_convolution (n j s : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (hj : j ≤ n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s (W.map (Int.castRingHom ℚ)) =
      ∑ l ∈ Finset.Icc s 9, ZetaNine.CoefficientMapJet.localCoefficient n j l *
        ((W.comp (ZetaNine.CoefficientMapJet.integerLocalU n j)).coeff (l - s) : ℚ) :=
  ZetaNine.CoefficientMapJet.integer_coefficient_convolution n j s hj hs1 hs9 W

#print axioms checked_original_local_convolution

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
  for name in [
    `ZetaNine.CoefficientMapJet.shiftedVariable,
    `ZetaNine.CoefficientMapJet.shiftedNumerator,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    `ZetaNine.CoefficientMapJet.localU,
    `ZetaNine.CoefficientMapJet.integerLocalU,
    `ZetaNine.CoefficientMapJet.clearedSeries,
    `ZetaNine.CoefficientMapJet.weightedClearedSeries,
    `ZetaNine.CoefficientMapJet.localCoefficient,
    `ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
    `ZetaNine.CoefficientMapJet.shiftedVariable_eval,
    `ZetaNine.CoefficientMapJet.shiftedNumerator_eval,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval,
    `ZetaNine.CoefficientMapJet.actual_local_rational_expression,
    `ZetaNine.CoefficientMapJet.localU_eval,
    `ZetaNine.CoefficientMapJet.localU_eq,
    `ZetaNine.CoefficientMapJet.integerLocalU_map,
    `ZetaNine.CoefficientMapJet.actual_weighted_local_rational_expression,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero,
    `ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity,
    `ZetaNine.CoefficientMapJet.clearedSeries_unique,
    `ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity,
    `ZetaNine.CoefficientMapJet.clearedSeries_constant,
    `ZetaNine.CoefficientMapJet.localCoefficient_nine,
    `ZetaNine.CoefficientMapJet.weightedLocalCoefficient_nine,
    `ZetaNine.CoefficientMapJet.coefficient_convolution,
    `ZetaNine.CoefficientMapJet.coefficient_convolution_explicit,
    `ZetaNine.CoefficientMapJet.integer_coefficient_convolution,
    `checked_original_local_convolution] do emit name
