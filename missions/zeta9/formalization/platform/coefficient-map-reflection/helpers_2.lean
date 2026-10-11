import Solutions.Sol_ZetaNine_CoefficientMapReflection_rho_one_zero_of_strong_proper
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
  emit "ZetaNine.CoefficientMapReflection.polePolynomial_reflection" `ZetaNine.CoefficientMapReflection.polePolynomial_reflection
  emit "ZetaNine.CoefficientMapReflection.partialBasis_simple_pole_top_coefficient" `ZetaNine.CoefficientMapReflection.partialBasis_simple_pole_top_coefficient
  emit "ZetaNine.CoefficientMapReflection.reflectionVariable_eval" `ZetaNine.CoefficientMapReflection.reflectionVariable_eval
  emit "ZetaNine.CoefficientMapReflection.shiftedWeightedNumerator_reflection" `ZetaNine.CoefficientMapReflection.shiftedWeightedNumerator_reflection
  emit "ZetaNine.CoefficientMapReflection.baseNumerator_reflection" `ZetaNine.CoefficientMapReflection.baseNumerator_reflection
  emit "ZetaNine.CoefficientMapReflection.product_reverse_range" `ZetaNine.CoefficientMapReflection.product_reverse_range
  emit "ZetaNine.CoefficientMapReflection.weightedNumerator_reflection" `ZetaNine.CoefficientMapReflection.weightedNumerator_reflection
  emit "ZetaNine.CoefficientMapReflection.local_shift_reflection" `ZetaNine.CoefficientMapReflection.local_shift_reflection
  emit "ZetaNine.CoefficientMapReflection.shiftedClearedDenominator_reflection" `ZetaNine.CoefficientMapReflection.shiftedClearedDenominator_reflection
  emit "ZetaNine.CoefficientMapReflection.local_coefficient_reflection" `ZetaNine.CoefficientMapReflection.local_coefficient_reflection
  emit "ZetaNine.CoefficientMapReflection.strong_proper_implies_proper" `ZetaNine.CoefficientMapReflection.strong_proper_implies_proper
  emit "ZetaNine.CoefficientMapReflection.checked_rho_one_zero_of_strong_proper" `ZetaNine.CoefficientMapReflection.checked_rho_one_zero_of_strong_proper
  emit "ZetaNine.CoefficientMapReflection.rescale_neg_one_C" `ZetaNine.CoefficientMapReflection.rescale_neg_one_C
  emit "ZetaNine.CoefficientMapReflection.actual_weightedR_reflection" `ZetaNine.CoefficientMapReflection.actual_weightedR_reflection
  emit "ZetaNine.CoefficientMapReflection.original_integer_quartic_strong_proper" `ZetaNine.CoefficientMapReflection.original_integer_quartic_strong_proper
  emit "ZetaNine.CoefficientMapReflection.partialBasis_natDegree" `ZetaNine.CoefficientMapReflection.partialBasis_natDegree
  emit "ZetaNine.CoefficientMapReflection.baseU_reflection" `ZetaNine.CoefficientMapReflection.baseU_reflection
  emit "ZetaNine.CoefficientMapReflection.sum_reverse_range" `ZetaNine.CoefficientMapReflection.sum_reverse_range
  emit "ZetaNine.CoefficientMapReflection.partialNumerator_top_coefficient_is_rho_one" `ZetaNine.CoefficientMapReflection.partialNumerator_top_coefficient_is_rho_one
  emit "ZetaNine.CoefficientMapReflection.partialBasis_higher_pole_top_coefficient" `ZetaNine.CoefficientMapReflection.partialBasis_higher_pole_top_coefficient
  emit "ZetaNine.CoefficientMapReflection.partialBasis_monic" `ZetaNine.CoefficientMapReflection.partialBasis_monic
  emit "ZetaNine.CoefficientMapReflection.product_reverse_erased_range" `ZetaNine.CoefficientMapReflection.product_reverse_erased_range
  emit "ZetaNine.CoefficientMapReflection.reflection_preserves_regular_points" `ZetaNine.CoefficientMapReflection.reflection_preserves_regular_points
  emit "ZetaNine.CoefficientMapReflection.original_integer_quartic_rho_one_zero" `ZetaNine.CoefficientMapReflection.original_integer_quartic_rho_one_zero
  emit "ZetaNine.CoefficientMapReflection.actual_local_series_reflection" `ZetaNine.CoefficientMapReflection.actual_local_series_reflection
  emit "ZetaNine.CoefficientMapReflection.rescale_neg_one_polynomial" `ZetaNine.CoefficientMapReflection.rescale_neg_one_polynomial
  emit "ZetaNine.CoefficientMapReflection.rho_even_order_zero" `ZetaNine.CoefficientMapReflection.rho_even_order_zero
  emit "ZetaNine.CoefficientMapReflection.clearedPolePolynomial_reflection" `ZetaNine.CoefficientMapReflection.clearedPolePolynomial_reflection
  emit "ZetaNine.CoefficientMapReflection.quartic_is_strong_proper" `ZetaNine.CoefficientMapReflection.quartic_is_strong_proper
  emit "ZetaNine.CoefficientMapReflection.clearedPolePolynomial_monic" `ZetaNine.CoefficientMapReflection.clearedPolePolynomial_monic
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
  emit "ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation" `ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation
  emit "solution" `solution
