import Solutions.Sol_ZetaNine_CoefficientMapFiniteSum_actual_finite_harmonic_identity
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
run_meta do
  let emit (label : String) (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Lean.Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axioms ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label", Json.str label), ("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("value", toJson value), ("axioms", toJson (axioms.toList.map Name.toString))]).compress
  emit "ZetaNine.CoefficientMapFiniteSum.harmonicPower_succ" `ZetaNine.CoefficientMapFiniteSum.harmonicPower_succ
  emit "ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity" `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity
  emit "ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd" `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd
  emit "ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum" `ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum
  emit "ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole" `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole
  emit "ZetaNine.CoefficientMapFiniteSum.checked_actual_finite_harmonic_identity" `ZetaNine.CoefficientMapFiniteSum.checked_actual_finite_harmonic_identity
  emit "ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted" `ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted
  emit "ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero" `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  emit "ZetaNine.CoefficientMapJet.shiftedVariable_eval" `ZetaNine.CoefficientMapJet.shiftedVariable_eval
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero
  emit "ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator_eval" `ZetaNine.CoefficientMapInjectivity.baseNumerator_eval
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift" `ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift
  emit "ZetaNine.CoefficientMapInjectivity.pole_factors_coprime" `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree" `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree" `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.baseU_natDegree" `ZetaNine.CoefficientMapInjectivity.baseU_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le" `ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le" `ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le
  emit "ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift" `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift
  emit "ZetaNine.CoefficientMapPartialFractions.localTruncation_comp_eq_sum" `ZetaNine.CoefficientMapPartialFractions.localTruncation_comp_eq_sum
  emit "ZetaNine.CoefficientMapPartialFractions.partialNumerator_eq_sum_blocks" `ZetaNine.CoefficientMapPartialFractions.partialNumerator_eq_sum_blocks
  emit "ZetaNine.CoefficientMapPartialFractions.partialBlock_comp_own_shift" `ZetaNine.CoefficientMapPartialFractions.partialBlock_comp_own_shift
  emit "ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd" `ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd
  emit "ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series" `ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series
  emit "ZetaNine.CoefficientMapPartialFractions.own_block_matches_nine_jets" `ZetaNine.CoefficientMapPartialFractions.own_block_matches_nine_jets
  emit "ZetaNine.CoefficientMapPartialFractions.different_block_pole_divisibility" `ZetaNine.CoefficientMapPartialFractions.different_block_pole_divisibility
  emit "ZetaNine.CoefficientMapPartialFractions.different_block_shift_X_pow_dvd" `ZetaNine.CoefficientMapPartialFractions.different_block_shift_X_pow_dvd
  emit "ZetaNine.CoefficientMapPartialFractions.full_candidate_matches_nine_jets" `ZetaNine.CoefficientMapPartialFractions.full_candidate_matches_nine_jets
  emit "ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility" `ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility
  emit "ZetaNine.CoefficientMapPartialFractions.denominator_divides_actual_candidate_difference" `ZetaNine.CoefficientMapPartialFractions.denominator_divides_actual_candidate_difference
  emit "ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree" `ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree
  emit "ZetaNine.CoefficientMapPartialFractions.localTruncation_natDegree_le" `ZetaNine.CoefficientMapPartialFractions.localTruncation_natDegree_le
  emit "ZetaNine.CoefficientMapPartialFractions.partialBlock_natDegree_le" `ZetaNine.CoefficientMapPartialFractions.partialBlock_natDegree_le
  emit "ZetaNine.CoefficientMapPartialFractions.partialNumerator_natDegree_le" `ZetaNine.CoefficientMapPartialFractions.partialNumerator_natDegree_le
  emit "ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions" `ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions
  emit "ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval" `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval
  emit "ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero" `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero
  emit "ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor" `ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor
  emit "ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation" `ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation
  emit "ZetaNine.CoefficientMapPartialFractions.partial_term_division" `ZetaNine.CoefficientMapPartialFractions.partial_term_division
  emit "ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions" `ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions
  emit "solution" `solution
