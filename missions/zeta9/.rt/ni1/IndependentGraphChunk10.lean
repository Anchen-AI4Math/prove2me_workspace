import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapSummation.zetaReal", "def"),
    ("ZetaNine.CoefficientMapSummation.exactL", "def"),
    ("ZetaNine.CoefficientMapSummation.actualSeries", "def"),
    ("ZetaNine.CoefficientMapSummation.actual_finite_odd_identity", "theorem"),
    ("ZetaNine.CoefficientMapSummation.sum_Icc_eq_sum_range_successor", "theorem"),
    ("ZetaNine.CoefficientMapSummation.harmonicPower_cast", "theorem"),
    ("ZetaNine.CoefficientMapSummation.harmonicPower_cast_eq_range", "theorem"),
    ("ZetaNine.CoefficientMapSummation.zetaReal_eq_tsum", "theorem"),
    ("ZetaNine.CoefficientMapSummation.harmonicPower_tendsto_zeta", "theorem"),
    ("ZetaNine.CoefficientMapSummation.shifted_reciprocal_tendsto_zero", "theorem"),
    ("ZetaNine.CoefficientMapSummation.harmonic_fixed_tail_tendsto_zero", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actual_shiftedTail_tendsto_zero", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actual_finiteL_tendsto_exactL", "theorem"),
    ("ZetaNine.CoefficientMapSummation.simple_pole_difference_identity", "theorem"),
    ("ZetaNine.CoefficientMapSummation.simple_pole_difference_summable", "theorem"),
    ("ZetaNine.CoefficientMapSummation.shifted_high_order_summable", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_eq_principal_parts", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_eq_cancelled_principal_parts", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_summable", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_norm_summable", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_partial_sums", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_hasSum_exactL", "theorem"),
    ("ZetaNine.CoefficientMapSummation.actualSeries_tsum_exactL", "theorem"),
    ("ZetaNine.CoefficientMapSummation.original_integer_quartic_exact_infinite_L", "theorem")]
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
