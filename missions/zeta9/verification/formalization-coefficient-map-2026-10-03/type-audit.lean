import missions.zeta9.formalization.CoefficientMap
import Lean

open Lean Meta
set_option pp.fullNames true
set_option pp.universes false

-- This imported statement asserts the complete actual-product endpoint,
-- without a coefficient-formula premise or an abstract partial-fraction input.
theorem checked_actual_leading (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ)) =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) :=
  ZetaNine.CoefficientMap.leadingPoleCoefficient_eq n j hj

#print axioms checked_actual_leading

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
    `ZetaNine.CoefficientMap.numerator,
    `ZetaNine.CoefficientMap.poleProduct,
    `ZetaNine.CoefficientMap.actualR,
    `ZetaNine.CoefficientMap.clearedPoleProduct,
    `ZetaNine.CoefficientMap.clearedR,
    `ZetaNine.CoefficientMap.leadingPoleCoefficient,
    `ZetaNine.CoefficientMap.weightedR,
    `ZetaNine.CoefficientMap.clearedWeightedR,
    `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient,
    `ZetaNine.CoefficientMap.poleProduct_factor,
    `ZetaNine.CoefficientMap.poleProduct_ne_zero,
    `ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero,
    `ZetaNine.CoefficientMap.clear_highest_pole,
    `ZetaNine.CoefficientMap.clear_weighted_highest_pole,
    `ZetaNine.CoefficientMap.rising_product,
    `ZetaNine.CoefficientMap.falling_product,
    `ZetaNine.CoefficientMap.clearedPoleProduct_eval,
    `ZetaNine.CoefficientMap.numerator_eval,
    `ZetaNine.CoefficientMap.leadingPoleCoefficient_eq,
    `ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even,
    `ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero,
    `ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer,
    `ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even,
    `ZetaNine.CoefficientMap.local_coordinate_identity,
    `ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate,
    `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq,
    `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even,
    `checked_actual_leading] do emit name
