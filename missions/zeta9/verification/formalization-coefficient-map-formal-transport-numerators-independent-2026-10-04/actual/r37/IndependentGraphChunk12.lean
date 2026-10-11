import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapTelescoper.prefixSum", "def"),
    ("ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient", "def"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper", "def"),
    ("ZetaNine.CoefficientMapTelescoper.telescoperNumerator", "def"),
    ("ZetaNine.CoefficientMapTelescoper.rootNode", "def"),
    ("ZetaNine.CoefficientMapTelescoper.rootPolynomial", "def"),
    ("ZetaNine.CoefficientMapTelescoper.prefixSum_succ", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.finite_cumulative_difference", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient_succ", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient_last_zero", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_as_sum_over_orders", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_difference_principal_parts", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.actual_weightedR_is_difference", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_positive_tendsto_zero", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.finite_sum_is_telescoper_boundary", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_at_one_zero", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.actual_weightedR_positive_zero", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_positive_zeros", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient_reflection", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_reflection", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_negative_zeros", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.cleared_term_division", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoperNumerator_natDegree_le", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.rootNode_injective", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.rootPolynomial_monic", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.rootPolynomial_eq_explicit_products", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.rootPolynomial_natDegree", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.telescoperNumerator_zero_at_nodes", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.all_kernel_nodes_divide_telescoperNumerator", "theorem"),
    ("ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound", "theorem")]
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
