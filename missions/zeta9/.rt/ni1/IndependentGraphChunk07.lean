import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial", "def"),
    ("ZetaNine.CoefficientMapPartialFractions.localTruncation", "def"),
    ("ZetaNine.CoefficientMapPartialFractions.partialBlock", "def"),
    ("ZetaNine.CoefficientMapPartialFractions.partialNumerator", "def"),
    ("ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries", "def"),
    ("ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_comp_shift", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.localTruncation_comp_eq_sum", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.partialNumerator_eq_sum_blocks", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.partialBlock_comp_own_shift", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.truncation_remainder_X_pow_dvd", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.polynomial_X_pow_dvd_of_series", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.own_block_matches_nine_jets", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.different_block_pole_divisibility", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.different_block_shift_X_pow_dvd", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.full_candidate_matches_nine_jets", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.shifted_divisibility_implies_pole_divisibility", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.denominator_divides_actual_candidate_difference", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.actual_series_from_shifted_numerator", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.candidateClearedSeries_denominator_identity", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.candidate_first_nine_coefficients", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.candidate_local_coefficients", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.clearedPolePolynomial_natDegree", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.localTruncation_natDegree_le", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.partialBlock_natDegree_le", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.partialNumerator_natDegree_le", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.actual_global_polynomial_partial_fractions", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.polePolynomial_eval_factor", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.actual_weighted_rational_representation", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.partial_term_division", "theorem"),
    ("ZetaNine.CoefficientMapPartialFractions.actual_global_partial_fractions", "theorem")]
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
