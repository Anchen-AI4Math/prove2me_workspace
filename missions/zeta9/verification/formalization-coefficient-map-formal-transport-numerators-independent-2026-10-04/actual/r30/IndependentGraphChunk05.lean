import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapJet.shiftedVariable", "def"),
    ("ZetaNine.CoefficientMapJet.shiftedNumerator", "def"),
    ("ZetaNine.CoefficientMapJet.shiftedClearedDenominator", "def"),
    ("ZetaNine.CoefficientMapJet.localU", "def"),
    ("ZetaNine.CoefficientMapJet.integerLocalU", "def"),
    ("ZetaNine.CoefficientMapJet.clearedSeries", "def"),
    ("ZetaNine.CoefficientMapJet.weightedClearedSeries", "def"),
    ("ZetaNine.CoefficientMapJet.localCoefficient", "def"),
    ("ZetaNine.CoefficientMapJet.weightedLocalCoefficient", "def"),
    ("ZetaNine.CoefficientMapJet.shiftedVariable_eval", "theorem"),
    ("ZetaNine.CoefficientMapJet.shiftedNumerator_eval", "theorem"),
    ("ZetaNine.CoefficientMapJet.shiftedClearedDenominator_eval", "theorem"),
    ("ZetaNine.CoefficientMapJet.actual_local_rational_expression", "theorem"),
    ("ZetaNine.CoefficientMapJet.localU_eval", "theorem"),
    ("ZetaNine.CoefficientMapJet.localU_eq", "theorem"),
    ("ZetaNine.CoefficientMapJet.integerLocalU_map", "theorem"),
    ("ZetaNine.CoefficientMapJet.actual_weighted_local_rational_expression", "theorem"),
    ("ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant", "theorem"),
    ("ZetaNine.CoefficientMapJet.shiftedClearedDenominator_constant_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMapJet.clearedSeries_denominator_identity", "theorem"),
    ("ZetaNine.CoefficientMapJet.clearedSeries_unique", "theorem"),
    ("ZetaNine.CoefficientMapJet.weightedClearedSeries_denominator_identity", "theorem"),
    ("ZetaNine.CoefficientMapJet.clearedSeries_constant", "theorem"),
    ("ZetaNine.CoefficientMapJet.localCoefficient_nine", "theorem"),
    ("ZetaNine.CoefficientMapJet.weightedLocalCoefficient_nine", "theorem"),
    ("ZetaNine.CoefficientMapJet.coefficient_convolution", "theorem"),
    ("ZetaNine.CoefficientMapJet.coefficient_convolution_explicit", "theorem"),
    ("ZetaNine.CoefficientMapJet.integer_coefficient_convolution", "theorem")]
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
