import missions.zeta9.formalization.CoefficientMapParameterShift
import Lean

-- Independent expected closed types. Prepared only; no compilation receipt.
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace IndependentParameterShiftExpected
open ZetaNine
open CoefficientMapKernelBridge CoefficientMapConnection CoefficientMapParameterShift

theorem parameterScale_value : parameterScale =
    (fun n : Nat => (((n : Rat) + 1) * ((n : Rat) + 2)) ^ 7) := rfl

theorem connectionRemainder_value : connectionRemainder =
    (fun (n : Nat) (q : Rat[X]) (t : Rat) =>
      CoefficientMap.actualR n t * (t - (n : Rat) - 1) / (t - 1) ^ 10 *
        q.eval ((connectionV n).eval t)) := rfl

theorem expected_positiveProduct_add_two :
    ∀ (n : Nat) (t : Rat), positiveProduct (n + 2) t =
      positiveProduct n t * (t - (n : Rat) - 1) * (t - (n : Rat) - 2) :=
  positiveProduct_add_two

theorem expected_positiveProduct_parameter_shift :
    ∀ (n : Nat) (t : Rat), positiveProduct (n + 2) (t - 1) * (t - 1) =
      positiveProduct n t * (t - (n : Rat) - 1) *
        (t - (n : Rat) - 2) * (t - (n : Rat) - 3) :=
  positiveProduct_parameter_shift

theorem expected_negativeProduct_add_two_sub_one :
    ∀ (n : Nat) (t : Rat), negativeProduct (n + 2) (t - 1) =
      negativeProduct n (t + 1) * (t + 2 * (n : Rat) + 2) *
        (t + 2 * (n : Rat) + 3) := negativeProduct_add_two_sub_one

theorem expected_negativeProduct_parameter_shift :
    ∀ (n : Nat) (t : Rat), negativeProduct (n + 2) (t - 1) * (t + (n : Rat) + 1) =
      negativeProduct n t * (t + 2 * (n : Rat) + 1) *
        (t + 2 * (n : Rat) + 2) * (t + 2 * (n : Rat) + 3) :=
  negativeProduct_parameter_shift

theorem expected_poleProduct_parameter_shift :
    ∀ (n : Nat) (t : Rat), CoefficientMap.poleProduct (n + 2) (t - 1) =
      (t - 1) * CoefficientMap.poleProduct n t * (t + (n : Rat) + 1) :=
  poleProduct_parameter_shift

theorem expected_factorial_parameter_shift :
    ∀ n : Nat, ((n + 2).factorial : Rat) ^ 7 =
      parameterScale n * (n.factorial : Rat) ^ 7 := factorial_parameter_shift

theorem expected_connectionZ_eval_factors :
    ∀ (n : Nat) (t : Rat), (connectionZ n).eval (t * (t + (n : Rat))) =
      ((t - (n : Rat) - 1) * (t + 2 * (n : Rat) + 1)) *
        ((t - (n : Rat) - 2) * (t + 2 * (n : Rat) + 2)) *
        ((t - (n : Rat) - 3) * (t + 2 * (n : Rat) + 3)) := connectionZ_eval_factors

theorem expected_numerator_parameter_shift :
    ∀ (n : Nat) (t : Rat), CoefficientMap.numerator (n + 2) (t - 1) *
      (t - 1) * (t + (n : Rat) + 1) = parameterScale n *
        CoefficientMap.numerator n t * (connectionZ n).eval (t * (t + (n : Rat))) :=
  numerator_parameter_shift

theorem expected_connectionD_eval_factors :
    ∀ (n : Nat) (t : Rat), (connectionD n).eval t =
      (t - 1) ^ 10 * (t + (n : Rat) + 1) ^ 10 := connectionD_eval_factors

theorem expected_shifted_regular_conditions :
    ∀ (n : Nat) (t : Rat), (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
      (∀ k ≤ n, t + (k : Rat) ≠ 0) ∧
      (∀ k ≤ n, t + 1 + (k : Rat) ≠ 0) ∧
      t - 1 ≠ 0 ∧ t ≠ 0 ∧ t + (n : Rat) + 1 ≠ 0 := shifted_regular_conditions

theorem expected_actual_R_parameter_shift :
    ∀ (n : Nat) (t : Rat), (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
      CoefficientMap.actualR (n + 2) (t - 1) * (connectionD n).eval t =
        parameterScale n * (connectionZ n).eval (t * (t + (n : Rat))) *
          CoefficientMap.actualR n t := actual_R_parameter_shift

theorem expected_connectionRemainder_successor :
    ∀ (n : Nat), 1 ≤ n → ∀ (q : Rat[X]) (t : Rat),
      (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
      connectionRemainder n q (t + 1) =
        CoefficientMap.actualR n t * (t + 2 * (n : Rat) + 1) /
          (t + (n : Rat) + 1) ^ 10 * q.eval ((t + 1) * (t + (n : Rat))) :=
  connectionRemainder_successor

theorem expected_connectionRemainder_difference :
    ∀ (n : Nat), 1 ≤ n → ∀ (q : Rat[X]) (t : Rat),
      (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
      connectionRemainder n q t - connectionRemainder n q (t + 1) =
        CoefficientMap.actualR n t * (connectionH n q).eval t / (connectionD n).eval t :=
  connectionRemainder_difference

theorem expected_actual_original_connection_transport :
    ∀ (n : Nat), 1 ≤ n → ∀ (r : Nat) (P q : Rat[X]),
      connectionD n * P.comp (connectionU n) + connectionH n q =
        (connectionTarget n r).comp (connectionU n) →
      ∀ t : Rat, (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
        CoefficientMap.actualR (n + 2) (t - 1) *
          (t * (t + (n : Rat)) - ((n : Rat) + 1)) ^ r =
        CoefficientMap.actualR n t * P.eval (t * (t + (n : Rat))) +
          (connectionRemainder n q t - connectionRemainder n q (t + 1)) :=
  actual_original_connection_transport

theorem expected_five_actual_connection_transports_exist_unique :
    ∀ (n : Nat), 1 ≤ n → ∀ r : Fin 5,
      ∃! pq : Rat[X] × Rat[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
        connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
          (connectionTarget n r.val).comp (connectionU n) ∧
        ∀ t : Rat, (∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) →
          CoefficientMap.actualR (n + 2) (t - 1) *
            (t * (t + (n : Rat)) - ((n : Rat) + 1)) ^ r.val =
          CoefficientMap.actualR n t * pq.1.eval (t * (t + (n : Rat))) +
            (connectionRemainder n pq.2 t - connectionRemainder n pq.2 (t + 1)) :=
  five_actual_connection_transports_exist_unique

end IndependentParameterShiftExpected

open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in [`IndependentParameterShiftExpected.parameterScale_value,
    `IndependentParameterShiftExpected.connectionRemainder_value,
    `IndependentParameterShiftExpected.expected_positiveProduct_add_two,
    `IndependentParameterShiftExpected.expected_positiveProduct_parameter_shift,
    `IndependentParameterShiftExpected.expected_negativeProduct_add_two_sub_one,
    `IndependentParameterShiftExpected.expected_negativeProduct_parameter_shift,
    `IndependentParameterShiftExpected.expected_poleProduct_parameter_shift,
    `IndependentParameterShiftExpected.expected_factorial_parameter_shift,
    `IndependentParameterShiftExpected.expected_connectionZ_eval_factors,
    `IndependentParameterShiftExpected.expected_numerator_parameter_shift,
    `IndependentParameterShiftExpected.expected_connectionD_eval_factors,
    `IndependentParameterShiftExpected.expected_shifted_regular_conditions,
    `IndependentParameterShiftExpected.expected_actual_R_parameter_shift,
    `IndependentParameterShiftExpected.expected_connectionRemainder_successor,
    `IndependentParameterShiftExpected.expected_connectionRemainder_difference,
    `IndependentParameterShiftExpected.expected_actual_original_connection_transport,
    `IndependentParameterShiftExpected.expected_five_actual_connection_transports_exist_unique] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("type_pp_diagnostic",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress

run_meta do
  for (sourceName, expectedName) in [(`ZetaNine.CoefficientMapParameterShift.positiveProduct_add_two, `IndependentParameterShiftExpected.expected_positiveProduct_add_two),(`ZetaNine.CoefficientMapParameterShift.positiveProduct_parameter_shift, `IndependentParameterShiftExpected.expected_positiveProduct_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.negativeProduct_add_two_sub_one, `IndependentParameterShiftExpected.expected_negativeProduct_add_two_sub_one),(`ZetaNine.CoefficientMapParameterShift.negativeProduct_parameter_shift, `IndependentParameterShiftExpected.expected_negativeProduct_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.poleProduct_parameter_shift, `IndependentParameterShiftExpected.expected_poleProduct_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.factorial_parameter_shift, `IndependentParameterShiftExpected.expected_factorial_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.connectionZ_eval_factors, `IndependentParameterShiftExpected.expected_connectionZ_eval_factors),(`ZetaNine.CoefficientMapParameterShift.numerator_parameter_shift, `IndependentParameterShiftExpected.expected_numerator_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.connectionD_eval_factors, `IndependentParameterShiftExpected.expected_connectionD_eval_factors),(`ZetaNine.CoefficientMapParameterShift.shifted_regular_conditions, `IndependentParameterShiftExpected.expected_shifted_regular_conditions),(`ZetaNine.CoefficientMapParameterShift.actual_R_parameter_shift, `IndependentParameterShiftExpected.expected_actual_R_parameter_shift),(`ZetaNine.CoefficientMapParameterShift.connectionRemainder_successor, `IndependentParameterShiftExpected.expected_connectionRemainder_successor),(`ZetaNine.CoefficientMapParameterShift.connectionRemainder_difference, `IndependentParameterShiftExpected.expected_connectionRemainder_difference),(`ZetaNine.CoefficientMapParameterShift.actual_original_connection_transport, `IndependentParameterShiftExpected.expected_actual_original_connection_transport),(`ZetaNine.CoefficientMapParameterShift.five_actual_connection_transports_exist_unique, `IndependentParameterShiftExpected.expected_five_actual_connection_transports_exist_unique)] do
    let actual ← getConstInfo sourceName
    let expected ← getConstInfo expectedName
    let eq ← isDefEq actual.type expected.type
    unless eq do throwError "Original and independent explicit type differ: {sourceName}"
    IO.println (Json.mkObj [("kind",Json.str "actual_whole_type_kernel_comparison"),
      ("source",Json.str sourceName.toString),("expected",Json.str expectedName.toString),
      ("type_kernel_equal",toJson eq),("actual_type_full_expr",Json.str (reprStr actual.type)),
      ("expected_type_full_expr",Json.str (reprStr expected.type))]).compress
