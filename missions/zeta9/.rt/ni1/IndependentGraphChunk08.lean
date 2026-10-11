import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapReflection.reflectionVariable", "def"),
    ("ZetaNine.CoefficientMapReflection.rho", "def"),
    ("ZetaNine.CoefficientMapReflection.StrongProperMultiplier", "def"),
    ("ZetaNine.CoefficientMapReflection.partialBasis", "def"),
    ("ZetaNine.CoefficientMapReflection.product_reverse_range", "theorem"),
    ("ZetaNine.CoefficientMapReflection.product_reverse_erased_range", "theorem"),
    ("ZetaNine.CoefficientMapReflection.sum_reverse_range", "theorem"),
    ("ZetaNine.CoefficientMapReflection.baseNumerator_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.baseU_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.weightedNumerator_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.polePolynomial_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.clearedPolePolynomial_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.reflectionVariable_eval", "theorem"),
    ("ZetaNine.CoefficientMapReflection.actual_weightedR_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.reflection_preserves_regular_points", "theorem"),
    ("ZetaNine.CoefficientMapReflection.local_shift_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.shiftedWeightedNumerator_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.shiftedClearedDenominator_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.rescale_neg_one_C", "theorem"),
    ("ZetaNine.CoefficientMapReflection.rescale_neg_one_polynomial", "theorem"),
    ("ZetaNine.CoefficientMapReflection.actual_local_series_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.local_coefficient_reflection", "theorem"),
    ("ZetaNine.CoefficientMapReflection.rho_even_order_zero", "theorem"),
    ("ZetaNine.CoefficientMapReflection.strong_proper_implies_proper", "theorem"),
    ("ZetaNine.CoefficientMapReflection.quartic_is_strong_proper", "theorem"),
    ("ZetaNine.CoefficientMapReflection.clearedPolePolynomial_monic", "theorem"),
    ("ZetaNine.CoefficientMapReflection.partialBasis_monic", "theorem"),
    ("ZetaNine.CoefficientMapReflection.partialBasis_natDegree", "theorem"),
    ("ZetaNine.CoefficientMapReflection.partialBasis_simple_pole_top_coefficient", "theorem"),
    ("ZetaNine.CoefficientMapReflection.partialBasis_higher_pole_top_coefficient", "theorem"),
    ("ZetaNine.CoefficientMapReflection.partialNumerator_top_coefficient_is_rho_one", "theorem"),
    ("ZetaNine.CoefficientMapReflection.rho_one_zero_of_strong_proper", "theorem"),
    ("ZetaNine.CoefficientMapReflection.original_integer_quartic_strong_proper", "theorem"),
    ("ZetaNine.CoefficientMapReflection.original_integer_quartic_rho_one_zero", "theorem")]
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
