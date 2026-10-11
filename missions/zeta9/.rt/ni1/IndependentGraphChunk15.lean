import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapConnection.connectionU", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionV", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionD", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionH", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionD_factor", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionV_simple_root", "theorem"),
    ("ZetaNine.CoefficientMapConnection.rootMultiplicity_le_natDegree_rat", "theorem"),
    ("ZetaNine.CoefficientMapConnection.rootMultiplicity_simple_composition", "theorem"),
    ("ZetaNine.CoefficientMapConnection.first_factor_eval_one_ne_zero", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connection_homogeneous_q_zero", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionU_comp_eq_zero", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionReflection", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionU_reflection", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionH_reflection", "theorem"),
    ("ZetaNine.CoefficientMapConnection.reflected_natDegree_even", "theorem"),
    ("ZetaNine.CoefficientMapConnection.reflected_even_coefficients_determine", "theorem"),
    ("ZetaNine.CoefficientMapConnection.coefficientPolynomial", "def"),
    ("ZetaNine.CoefficientMapConnection.coefficientPolynomial_coeff", "theorem"),
    ("ZetaNine.CoefficientMapConnection.coefficientPolynomial_add", "theorem"),
    ("ZetaNine.CoefficientMapConnection.coefficientPolynomial_smul", "theorem"),
    ("ZetaNine.CoefficientMapConnection.coefficientPolynomial_degree", "theorem"),
    ("ZetaNine.CoefficientMapConnection.inputP", "def"),
    ("ZetaNine.CoefficientMapConnection.inputQ", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator_reflection", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator_degree", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator_add", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator_smul", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionLinearMap", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionLinearMap_injective", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connection_reflected_target_exists_unique", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionOperator_sub", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connection_original_system_exists_unique", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connectionZ", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionTarget", "def"),
    ("ZetaNine.CoefficientMapConnection.connectionTarget_degree", "theorem"),
    ("ZetaNine.CoefficientMapConnection.connection_five_systems_unique", "theorem")]
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
