import Solutions.Sol_ZetaNine_CoefficientMap_leadingPoleCoefficient_eq
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
  emit "ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even" `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even
  emit "ZetaNine.CoefficientMap.clear_highest_pole" `ZetaNine.CoefficientMap.clear_highest_pole
  emit "ZetaNine.CoefficientMap.clear_weighted_highest_pole" `ZetaNine.CoefficientMap.clear_weighted_highest_pole
  emit "ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate" `ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate
  emit "ZetaNine.CoefficientMap.clearedPoleProduct_eval" `ZetaNine.CoefficientMap.clearedPoleProduct_eval
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even" `ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero" `ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero
  emit "ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq" `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq
  emit "ZetaNine.CoefficientMap.poleProduct_factor" `ZetaNine.CoefficientMap.poleProduct_factor
  emit "ZetaNine.CoefficientMap.rising_product" `ZetaNine.CoefficientMap.rising_product
  emit "ZetaNine.CoefficientMap.falling_product" `ZetaNine.CoefficientMap.falling_product
  emit "ZetaNine.CoefficientMap.local_coordinate_identity" `ZetaNine.CoefficientMap.local_coordinate_identity
  emit "ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer" `ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer
  emit "ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero" `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  emit "ZetaNine.CoefficientMap.poleProduct_ne_zero" `ZetaNine.CoefficientMap.poleProduct_ne_zero
  emit "ZetaNine.CoefficientMap.numerator_eval" `ZetaNine.CoefficientMap.numerator_eval
  emit "ZetaNine.CoefficientMap.checked_leadingPoleCoefficient_eq" `ZetaNine.CoefficientMap.checked_leadingPoleCoefficient_eq
  emit "ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even" `ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even
  emit "solution" `solution
