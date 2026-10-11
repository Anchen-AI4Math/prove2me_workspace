import missions.zeta9.formalization.CoefficientMapFiniteSum
import Lean
open Lean Meta
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  for name in [
    `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero,
    `ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd,
    `ZetaNine.CoefficientMapFiniteSum.harmonicPower_succ,
    `ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted,
    `ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_eval,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.baseU_natDegree,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree,
    `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift,
    `ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero,
    `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval,
    `ZetaNine.CoefficientMapJet.shiftedVariable_eval,
    `ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity,
    `ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions,
    `ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions,
    `ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation,
    `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift,
    `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree,
    `ZetaNine.CoefficientMapPartialFractions.denominator_divides_actual_candidate_difference,
    `ZetaNine.CoefficientMapPartialFractions.different_block_pole_divisibility,
    `ZetaNine.CoefficientMapPartialFractions.different_block_shift_X_pow_dvd,
    `ZetaNine.CoefficientMapPartialFractions.full_candidate_matches_nine_jets,
    `ZetaNine.CoefficientMapPartialFractions.localTruncation_comp_eq_sum,
    `ZetaNine.CoefficientMapPartialFractions.localTruncation_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.own_block_matches_nine_jets,
    `ZetaNine.CoefficientMapPartialFractions.partialBlock_comp_own_shift,
    `ZetaNine.CoefficientMapPartialFractions.partialBlock_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.partialNumerator_eq_sum_blocks,
    `ZetaNine.CoefficientMapPartialFractions.partialNumerator_natDegree_le,
    `ZetaNine.CoefficientMapPartialFractions.partial_term_division,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor,
    `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero,
    `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series,
    `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility,
    `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
