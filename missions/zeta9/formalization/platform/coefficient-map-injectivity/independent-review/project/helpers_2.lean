import Solutions.Sol_ZetaNine_CoefficientMapInjectivity_quartic_is_proper
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
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree" `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.baseU_natDegree" `ZetaNine.CoefficientMapInjectivity.baseU_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le" `ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le
  emit "ZetaNine.CoefficientMapInjectivity.local_coefficients_injective" `ZetaNine.CoefficientMapInjectivity.local_coefficients_injective
  emit "ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_pole_divisibility" `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_pole_divisibility
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator_ne_zero" `ZetaNine.CoefficientMapInjectivity.baseNumerator_ne_zero
  emit "ZetaNine.CoefficientMapInjectivity.weightedLocalCoefficient_sub" `ZetaNine.CoefficientMapInjectivity.weightedLocalCoefficient_sub
  emit "ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_shifted_numerator_divisibility" `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_shifted_numerator_divisibility
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator_zero_implies_multiplier_zero" `ZetaNine.CoefficientMapInjectivity.weightedNumerator_zero_implies_multiplier_zero
  emit "ZetaNine.CoefficientMapInjectivity.checked_quartic_is_proper" `ZetaNine.CoefficientMapInjectivity.checked_quartic_is_proper
  emit "ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree" `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree
  emit "ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective" `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective
  emit "ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero" `ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero
  emit "ZetaNine.CoefficientMapInjectivity.baseNumerator_eval" `ZetaNine.CoefficientMapInjectivity.baseNumerator_eval
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le" `ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le
  emit "ZetaNine.CoefficientMapInjectivity.pole_factors_coprime" `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime
  emit "ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift" `ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift
  emit "ZetaNine.CoefficientMapInjectivity.all_zero_jets_imply_full_denominator_divisibility" `ZetaNine.CoefficientMapInjectivity.all_zero_jets_imply_full_denominator_divisibility
  emit "ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero" `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  emit "ZetaNine.CoefficientMapJet.shiftedVariable_eval" `ZetaNine.CoefficientMapJet.shiftedVariable_eval
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant
  emit "ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero" `ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero
  emit "ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity
  emit "ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity" `ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity
  emit "solution" `solution
