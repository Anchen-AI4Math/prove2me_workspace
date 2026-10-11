import Solutions.Sol_ZetaNine_CoefficientMapConnection_connection_five_systems_unique
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let emit (label : String) (name : Name) : Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let type ← Meta.ppExpr ci.type
    let value ← match ci with
      | .defnInfo d => pure (some (← Meta.ppExpr d.value).pretty)
      | _ => pure none
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("label",Json.str label),("declaration",Json.str name.toString),
      ("type",Json.str type.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson value),("axioms",toJson (axs.toList.map Name.toString))]).compress
  emit "ZetaNine.CoefficientMapConnection.connectionU" `ZetaNine.CoefficientMapConnection.connectionU
  emit "ZetaNine.CoefficientMapConnection.connectionV" `ZetaNine.CoefficientMapConnection.connectionV
  emit "ZetaNine.CoefficientMapConnection.connectionD" `ZetaNine.CoefficientMapConnection.connectionD
  emit "ZetaNine.CoefficientMapConnection.connectionH" `ZetaNine.CoefficientMapConnection.connectionH
  emit "ZetaNine.CoefficientMapConnection.connectionD_factor" `ZetaNine.CoefficientMapConnection.connectionD_factor
  emit "ZetaNine.CoefficientMapConnection.connectionV_simple_root" `ZetaNine.CoefficientMapConnection.connectionV_simple_root
  emit "ZetaNine.CoefficientMapConnection.rootMultiplicity_le_natDegree_rat" `ZetaNine.CoefficientMapConnection.rootMultiplicity_le_natDegree_rat
  emit "ZetaNine.CoefficientMapConnection.rootMultiplicity_simple_composition" `ZetaNine.CoefficientMapConnection.rootMultiplicity_simple_composition
  emit "ZetaNine.CoefficientMapConnection.first_factor_eval_one_ne_zero" `ZetaNine.CoefficientMapConnection.first_factor_eval_one_ne_zero
  emit "ZetaNine.CoefficientMapConnection.connection_homogeneous_q_zero" `ZetaNine.CoefficientMapConnection.connection_homogeneous_q_zero
  emit "ZetaNine.CoefficientMapConnection.connectionU_comp_eq_zero" `ZetaNine.CoefficientMapConnection.connectionU_comp_eq_zero
  emit "ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero" `ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero
  emit "ZetaNine.CoefficientMapConnection.connectionReflection" `ZetaNine.CoefficientMapConnection.connectionReflection
  emit "ZetaNine.CoefficientMapConnection.connectionU_reflection" `ZetaNine.CoefficientMapConnection.connectionU_reflection
  emit "ZetaNine.CoefficientMapConnection.connectionH_reflection" `ZetaNine.CoefficientMapConnection.connectionH_reflection
  emit "ZetaNine.CoefficientMapConnection.reflected_natDegree_even" `ZetaNine.CoefficientMapConnection.reflected_natDegree_even
  emit "ZetaNine.CoefficientMapConnection.reflected_even_coefficients_determine" `ZetaNine.CoefficientMapConnection.reflected_even_coefficients_determine
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial" `ZetaNine.CoefficientMapConnection.coefficientPolynomial
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial_coeff" `ZetaNine.CoefficientMapConnection.coefficientPolynomial_coeff
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial_add" `ZetaNine.CoefficientMapConnection.coefficientPolynomial_add
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial_smul" `ZetaNine.CoefficientMapConnection.coefficientPolynomial_smul
  emit "ZetaNine.CoefficientMapConnection.coefficientPolynomial_degree" `ZetaNine.CoefficientMapConnection.coefficientPolynomial_degree
  emit "ZetaNine.CoefficientMapConnection.inputP" `ZetaNine.CoefficientMapConnection.inputP
  emit "ZetaNine.CoefficientMapConnection.inputQ" `ZetaNine.CoefficientMapConnection.inputQ
  emit "ZetaNine.CoefficientMapConnection.connectionOperator" `ZetaNine.CoefficientMapConnection.connectionOperator
  emit "ZetaNine.CoefficientMapConnection.connectionOperator_reflection" `ZetaNine.CoefficientMapConnection.connectionOperator_reflection
  emit "ZetaNine.CoefficientMapConnection.connectionOperator_degree" `ZetaNine.CoefficientMapConnection.connectionOperator_degree
  emit "ZetaNine.CoefficientMapConnection.connectionOperator_add" `ZetaNine.CoefficientMapConnection.connectionOperator_add
  emit "ZetaNine.CoefficientMapConnection.connectionOperator_smul" `ZetaNine.CoefficientMapConnection.connectionOperator_smul
  emit "ZetaNine.CoefficientMapConnection.connectionLinearMap" `ZetaNine.CoefficientMapConnection.connectionLinearMap
  emit "ZetaNine.CoefficientMapConnection.connectionLinearMap_injective" `ZetaNine.CoefficientMapConnection.connectionLinearMap_injective
  emit "ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective" `ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective
  emit "ZetaNine.CoefficientMapConnection.connection_reflected_target_exists_unique" `ZetaNine.CoefficientMapConnection.connection_reflected_target_exists_unique
  emit "ZetaNine.CoefficientMapConnection.connectionOperator_sub" `ZetaNine.CoefficientMapConnection.connectionOperator_sub
  emit "ZetaNine.CoefficientMapConnection.connection_original_system_exists_unique" `ZetaNine.CoefficientMapConnection.connection_original_system_exists_unique
  emit "ZetaNine.CoefficientMapConnection.connectionZ" `ZetaNine.CoefficientMapConnection.connectionZ
  emit "ZetaNine.CoefficientMapConnection.connectionTarget" `ZetaNine.CoefficientMapConnection.connectionTarget
  emit "ZetaNine.CoefficientMapConnection.connectionTarget_degree" `ZetaNine.CoefficientMapConnection.connectionTarget_degree
  emit "ZetaNine.CoefficientMapConnection.connection_five_systems_unique" `ZetaNine.CoefficientMapConnection.checked_connection_five_systems_unique
