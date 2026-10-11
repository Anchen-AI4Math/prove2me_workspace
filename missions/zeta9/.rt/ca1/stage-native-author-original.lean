import missions.zeta9.formalization.CoefficientMapConnection
import Lean
open Lean
set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let emit (name : Name) : Lean.Meta.MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let (kind, val, raw) ← match ci with
      | .defnInfo d => pure ("def", some (← Lean.Meta.ppExpr d.value).pretty, some (reprStr d.value))
      | .thmInfo _ => pure ("theorem", none, none)
      | _ => pure ("other", none, none)
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),("kind",Json.str kind),
      ("type",Json.str typ.pretty),("type_expression_repr",Json.str (reprStr ci.type)),
      ("value",toJson val),("definition_expression_repr",toJson raw),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
  emit `ZetaNine.CoefficientMapConnection.connectionU
  emit `ZetaNine.CoefficientMapConnection.connectionV
  emit `ZetaNine.CoefficientMapConnection.connectionD
  emit `ZetaNine.CoefficientMapConnection.connectionH
  emit `ZetaNine.CoefficientMapConnection.connectionD_factor
  emit `ZetaNine.CoefficientMapConnection.connectionV_simple_root
  emit `ZetaNine.CoefficientMapConnection.rootMultiplicity_le_natDegree_rat
  emit `ZetaNine.CoefficientMapConnection.rootMultiplicity_simple_composition
  emit `ZetaNine.CoefficientMapConnection.first_factor_eval_one_ne_zero
  emit `ZetaNine.CoefficientMapConnection.connection_homogeneous_q_zero
  emit `ZetaNine.CoefficientMapConnection.connectionU_comp_eq_zero
  emit `ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero
  emit `ZetaNine.CoefficientMapConnection.connectionReflection
  emit `ZetaNine.CoefficientMapConnection.connectionU_reflection
  emit `ZetaNine.CoefficientMapConnection.connectionH_reflection
  emit `ZetaNine.CoefficientMapConnection.reflected_natDegree_even
  emit `ZetaNine.CoefficientMapConnection.reflected_even_coefficients_determine
  emit `ZetaNine.CoefficientMapConnection.coefficientPolynomial
  emit `ZetaNine.CoefficientMapConnection.coefficientPolynomial_coeff
  emit `ZetaNine.CoefficientMapConnection.coefficientPolynomial_add
  emit `ZetaNine.CoefficientMapConnection.coefficientPolynomial_smul
  emit `ZetaNine.CoefficientMapConnection.coefficientPolynomial_degree
  emit `ZetaNine.CoefficientMapConnection.inputP
  emit `ZetaNine.CoefficientMapConnection.inputQ
  emit `ZetaNine.CoefficientMapConnection.connectionOperator
  emit `ZetaNine.CoefficientMapConnection.connectionOperator_reflection
  emit `ZetaNine.CoefficientMapConnection.connectionOperator_degree
  emit `ZetaNine.CoefficientMapConnection.connectionOperator_add
  emit `ZetaNine.CoefficientMapConnection.connectionOperator_smul
  emit `ZetaNine.CoefficientMapConnection.connectionLinearMap
  emit `ZetaNine.CoefficientMapConnection.connectionLinearMap_injective
  emit `ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective
  emit `ZetaNine.CoefficientMapConnection.connection_reflected_target_exists_unique
  emit `ZetaNine.CoefficientMapConnection.connectionOperator_sub
  emit `ZetaNine.CoefficientMapConnection.connection_original_system_exists_unique
  emit `ZetaNine.CoefficientMapConnection.connectionZ
  emit `ZetaNine.CoefficientMapConnection.connectionTarget
  emit `ZetaNine.CoefficientMapConnection.connectionTarget_degree
  emit `ZetaNine.CoefficientMapConnection.connection_five_systems_unique
