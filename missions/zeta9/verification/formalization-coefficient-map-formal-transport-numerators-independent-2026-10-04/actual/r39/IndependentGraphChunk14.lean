import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
open Lean Meta
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option pp.proofs true
set_option pp.fullNames true
run_meta do
  let specs : List (String × String) := [("ZetaNine.CoefficientMapKernelBridge.positiveProduct", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.negativeProduct", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.aValue", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.bValue", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.finite_product_shift_identity", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.positiveProduct_shift", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.negativeProduct_shift", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.numerator_shift_identity", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.poleProduct_shift_identity", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.actual_R_shift_A_equals_R_B", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.rootPolynomial_numerator_factor", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.poleProduct_last_factor", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.actual_R_A_equals_Pzero", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.telescoper_quotient_as_R_A", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.actual_R_ne_zero_above_n", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.kernel_actual_polynomial_relation", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_kernel_zero", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.original_quartic_aggregate_injective", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_injective", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.original_five_dimensional_map_bijective", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.actualAggregateEquiv", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.every_exact_formal_output_has_unique_quartic", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.prescribedL", "def"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_natDegree_le", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_aggregate", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_unique", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_nonzero_of_output_nonzero", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_exact_L", "theorem"),
    ("ZetaNine.CoefficientMapKernelBridge.inverseMultiplier_actual_HasSum_and_absolute", "theorem")]
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
