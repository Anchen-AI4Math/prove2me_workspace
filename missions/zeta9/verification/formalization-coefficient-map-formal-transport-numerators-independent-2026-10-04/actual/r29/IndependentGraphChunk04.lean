import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMap.numerator", "def"),
    ("ZetaNine.CoefficientMap.poleProduct", "def"),
    ("ZetaNine.CoefficientMap.actualR", "def"),
    ("ZetaNine.CoefficientMap.clearedPoleProduct", "def"),
    ("ZetaNine.CoefficientMap.clearedR", "def"),
    ("ZetaNine.CoefficientMap.leadingPoleCoefficient", "def"),
    ("ZetaNine.CoefficientMap.weightedR", "def"),
    ("ZetaNine.CoefficientMap.clearedWeightedR", "def"),
    ("ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient", "def"),
    ("ZetaNine.CoefficientMap.poleProduct_factor", "theorem"),
    ("ZetaNine.CoefficientMap.poleProduct_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMap.clear_highest_pole", "theorem"),
    ("ZetaNine.CoefficientMap.clear_weighted_highest_pole", "theorem"),
    ("ZetaNine.CoefficientMap.rising_product", "theorem"),
    ("ZetaNine.CoefficientMap.falling_product", "theorem"),
    ("ZetaNine.CoefficientMap.clearedPoleProduct_eval", "theorem"),
    ("ZetaNine.CoefficientMap.numerator_eval", "theorem"),
    ("ZetaNine.CoefficientMap.leadingPoleCoefficient_eq", "theorem"),
    ("ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even", "theorem"),
    ("ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer", "theorem"),
    ("ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even", "theorem"),
    ("ZetaNine.CoefficientMap.local_coordinate_identity", "theorem"),
    ("ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate", "theorem"),
    ("ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq", "theorem"),
    ("ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even", "theorem")]
  let env ← getEnv
  let constants := env.constants.toList
  for (wanted, sourceKind) in specs do
    let found := constants.filter fun (name, _) =>
      name.toString == wanted || name.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Exact source declaration resolution failed {wanted}"
    let (name, ci) := found.head!
    let actualKind := match ci with
      | .defnInfo _ => "definition"
      | .thmInfo _ => "proof"
      | _ => "other"
    let expectedKind := if sourceKind == "def" || sourceKind == "abbrev" then "definition" else "proof"
    unless actualKind == expectedKind do throwError "Source declaration kind mismatch {name}"
    let axioms ← collectAxioms name
    unless axioms.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard source axiom {name}"
    let typePP ← ppExpr ci.type
    let value := ci.value? (allowOpaque := true)
    IO.println (Json.mkObj [("kind",Json.str "actual_source_declaration"),
      ("source_kind",Json.str sourceKind),("source_name",Json.str wanted),
      ("actual_name",Json.str name.toString),("full_type_expr",Json.str (reprStr ci.type)),
      ("full_value_expr",Json.str (reprStr value)),("full_type_pp_diagnostic",Json.str typePP.pretty),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
