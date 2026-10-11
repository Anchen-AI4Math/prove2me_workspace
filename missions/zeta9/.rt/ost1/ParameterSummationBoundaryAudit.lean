import missions.zeta9.formalization.CoefficientMapParameterSummationTransport
import IndependentExprDagV3
import Lean
noncomputable section
open scoped BigOperators Matrix
open Polynomial
open ZetaNine
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapMatrix
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportBounds ZetaNine.CoefficientMapFormalTransportOutputs
open ZetaNine.CoefficientMapParameterSummationTransport

namespace ParameterSummationAuthorBoundary

theorem n1_exact_r0 :
    exactL (1 + 2) (X ^ (0 : Fin 5).val) = exactL 1 (connectionP 1 (0 : Fin 5)) :=
  actual_chosen_exactL_transport 1 (by decide) (0 : Fin 5)

theorem n2_HasSum_r0 :
    HasSum (actualSeries (2 + 2) (X ^ (0 : Fin 5).val)) (exactL 2 (connectionP 2 (0 : Fin 5))) ∧
      HasSum (actualSeries 2 (connectionP 2 (0 : Fin 5))) (exactL 2 (connectionP 2 (0 : Fin 5))) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (X ^ (0 : Fin 5).val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (connectionP 2 (0 : Fin 5)) t‖) :=
  actual_chosen_HasSum_transport 2 (by decide) (by decide) (0 : Fin 5)

theorem n2_HasSum_r4 :
    HasSum (actualSeries (2 + 2) (X ^ (4 : Fin 5).val)) (exactL 2 (connectionP 2 (4 : Fin 5))) ∧
      HasSum (actualSeries 2 (connectionP 2 (4 : Fin 5))) (exactL 2 (connectionP 2 (4 : Fin 5))) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (X ^ (4 : Fin 5).val) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (connectionP 2 (4 : Fin 5)) t‖) :=
  actual_chosen_HasSum_transport 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_tsum_r4 :
    (∑' t : ℕ, actualSeries (2 + 2) (X ^ (4 : Fin 5).val) t) =
      ∑' t : ℕ, actualSeries 2 (connectionP 2 (4 : Fin 5)) t :=
  actual_chosen_tsum_transport 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_transfer_r0 :
    transferMultiplier 2 (X ^ (0 : Fin 5).val) = connectionP 2 (0 : Fin 5) :=
  chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (0 : Fin 5)

theorem n2_transfer_r4 :
    transferMultiplier 2 (X ^ (4 : Fin 5).val) = connectionP 2 (4 : Fin 5) :=
  chosen_transferMultiplier_eq_connectionP 2 (by decide) (by decide) (4 : Fin 5)

theorem n2_selected_B :
    HasSum (actualSeries (2 + 2) (selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 1 0)) (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) 1 0)) (((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 1 0) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) 1 0) t‖) :=
  selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) 1 0

theorem n2_selected_A :
    HasSum (actualSeries (2 + 2) (selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 0 1)) (((0 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * zetaReal 9) ∧
      HasSum (actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) 0 1)) (((0 : ℤ) : ℝ) + ((1 : ℤ) : ℝ) * zetaReal 9) ∧
      Summable (fun t : ℕ => ‖actualSeries (2 + 2) (selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 0 1) t‖) ∧
      Summable (fun t : ℕ => ‖actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) 0 1) t‖) :=
  selectedIntegerMultiplier_parameter_HasSum 2 (by decide) (by decide) 0 1

theorem n2_selected_tsum :
    (∑' t : ℕ, actualSeries (2 + 2) (selectedIntegerMultiplier (2 + 2) (by decide) (even_add_two 2 (by decide)) 1 1) t) =
      ∑' t : ℕ, actualSeries 2 (selectedIntegerMultiplier 2 (by decide) (by decide) 1 1) t :=
  selectedIntegerMultiplier_parameter_tsum 2 (by decide) (by decide) 1 1

end ParameterSummationAuthorBoundary
open Lean Meta
set_option maxHeartbeats 0
set_option maxRecDepth 20000
run_meta do
  for name in [`ParameterSummationAuthorBoundary.n1_exact_r0,`ParameterSummationAuthorBoundary.n2_HasSum_r0,`ParameterSummationAuthorBoundary.n2_HasSum_r4,`ParameterSummationAuthorBoundary.n2_tsum_r4,`ParameterSummationAuthorBoundary.n2_transfer_r0,`ParameterSummationAuthorBoundary.n2_transfer_r4,`ParameterSummationAuthorBoundary.n2_selected_B,`ParameterSummationAuthorBoundary.n2_selected_A,`ParameterSummationAuthorBoundary.n2_selected_tsum] do
    let .thmInfo info ← getConstInfo name | throwError "Boundary is not a theorem"
    let axioms ← collectAxioms name
    let allowed : List Name := [`propext,`Classical.choice,`Quot.sound]
    unless axioms.toList.all allowed.contains do throwError "Nonstandard boundary axioms"
    let dag ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip info.type info.value)
    IO.println (Json.mkObj [("kind",Json.str "actual_closed_boundary"),
      ("declaration",Json.str name.toString),("full_type_and_proof_expression_dag",dag),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
