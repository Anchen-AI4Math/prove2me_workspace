import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapKernelBridge CoefficientMapParameterShift
open CoefficientMapInjectivity CoefficientMapPartialFractions
namespace NumeratorsIndependentWholeTypes
theorem expected_positiveProduct_remainder_cancellation : ∀ (n : ℕ) (t : ℚ),
    positiveProduct n t * (t - (n : ℚ) - 1) =
      (t - 1) * ∏ i ∈ range n, (t - ((i : ℚ) + 2)) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.positiveProduct_remainder_cancellation

theorem expected_remainderNumerator_eval : ∀ (n : ℕ) (q : ℚ[X]) (t : ℚ),
    (remainderNumerator n q).eval t =
      (n.factorial : ℚ) ^ 7 *
        (∏ i ∈ range n, (t - ((i : ℚ) + 2))) *
        negativeProduct n t * q.eval ((CoefficientMapConnection.connectionV n).eval t) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_eval

theorem expected_remainderNumerator_actual_cancellation : ∀ (n : ℕ) (q : ℚ[X]) (t : ℚ),
    CoefficientMap.numerator n t * (t - (n : ℚ) - 1) *
        q.eval ((CoefficientMapConnection.connectionV n).eval t) =
      (t - 1) * (remainderNumerator n q).eval t :=
  ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_actual_cancellation

theorem expected_connectionRemainder_as_actual_numerator : ∀ (n : ℕ) (q : ℚ[X]) (t : ℚ)
    (hm : t - 1 ≠ 0) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0),
    connectionRemainder n q t =
      (remainderNumerator n q).eval t /
        ((t - 1) * (polePolynomial n).eval t) ^ 9 :=
  ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_as_actual_numerator

theorem expected_polePolynomial_successor_eval : ∀ (n : ℕ) (t : ℚ),
    (polePolynomial (n + 1)).eval t =
      (polePolynomial n).eval t * (t + ((n : ℚ) + 1)) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_eval

theorem expected_polePolynomial_successor_shift_eval : ∀ (n : ℕ) (x : ℚ),
    (polePolynomial (n + 1)).eval x =
      x * (polePolynomial n).eval (x + 1) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift_eval

theorem expected_polePolynomial_add_two_shift_eval : ∀ (n : ℕ) (x : ℚ),
    (polePolynomial (n + 2)).eval x =
      x * (polePolynomial n).eval (x + 1) * (x + ((n : ℚ) + 2)) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift_eval

theorem expected_polePolynomial_successor_shift : ∀ (n : ℕ),
    polePolynomial (n + 1) = X * (polePolynomial n).comp (X + 1) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift

theorem expected_polePolynomial_add_two_shift : ∀ (n : ℕ),
    polePolynomial (n + 2) =
      X * (polePolynomial n).comp (X + 1) * (X + C ((n : ℚ) + 2)) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift

theorem expected_connectionRemainder_shifted_as_actual_numerator : ∀ (n : ℕ) (q : ℚ[X]) (x : ℚ)
    (hregular : ∀ k ≤ n + 1, x + (k : ℚ) ≠ 0),
    connectionRemainder n q (x + 1) =
      (shiftedRemainderNumerator n q).eval x / (polePolynomial (n + 1)).eval x ^ 9 :=
  ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_shifted_as_actual_numerator

theorem expected_connectionRemainder_eval_two : ∀ (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X]),
    connectionRemainder n q 2 = 0 :=
  ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_eval_two

theorem expected_actual_chosen_connection_transport_positive : ∀ (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x),
    CoefficientMap.weightedR (n + 2) (X ^ r.val) x =
      CoefficientMap.weightedR n (connectionP n r) (x + 1) +
        (connectionRemainder n (connectionQ n r) (x + 1) -
          connectionRemainder n (connectionQ n r) (x + 1 + 1)) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_connection_transport_positive

theorem expected_three_denominator_combination : ∀ (B C D x y M : ℚ)
    (hx : x ≠ 0) (hy : y ≠ 0) (hM : M ≠ 0),
    B / M ^ 9 + (C / (x * M) ^ 9 - D / (M * y) ^ 9) =
      (x ^ 9 * y ^ 9 * B + y ^ 9 * C - x ^ 9 * D) / (x * M * y) ^ 9 :=
  by
    intro B C D x y M hx hy hM
    field_simp [hx, hy, hM]
    <;> ring

theorem expected_actual_chosen_cleared_numerator_transport_eval : ∀ (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (x : ℚ) (hx : 0 < x),
    (weightedNumerator (n + 2) (X ^ r.val)).eval x =
      x ^ 9 * (x + ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).eval (x + 1) +
        (x + ((n : ℚ) + 2)) ^ 9 *
          (shiftedRemainderNumerator n (connectionQ n r)).eval x -
        x ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).eval (x + 1) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport_eval

theorem expected_actual_chosen_cleared_numerator_transport : ∀ (n : ℕ) (hn : 1 ≤ n) (r : Fin 5),
    weightedNumerator (n + 2) (X ^ r.val) =
      X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 *
          (weightedNumerator n (connectionP n r)).comp (X + 1) +
        (X + C ((n : ℚ) + 2)) ^ 9 *
          shiftedRemainderNumerator n (connectionQ n r) -
        X ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).comp (X + 1) :=
  ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport

end NumeratorsIndependentWholeTypes
open Lean Meta
run_meta do
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.positiveProduct_remainder_cancellation"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_positiveProduct_remainder_cancellation
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_positiveProduct_remainder_cancellation
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_positiveProduct_remainder_cancellation"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_eval"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_remainderNumerator_eval
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_remainderNumerator_eval
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_remainderNumerator_eval"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.remainderNumerator_actual_cancellation"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_remainderNumerator_actual_cancellation
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_remainderNumerator_actual_cancellation
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_remainderNumerator_actual_cancellation"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_as_actual_numerator"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_connectionRemainder_as_actual_numerator
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_connectionRemainder_as_actual_numerator
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_connectionRemainder_as_actual_numerator"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_eval"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_eval
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_eval
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_eval"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift_eval"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift_eval
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift_eval
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift_eval"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift_eval"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift_eval
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift_eval
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift_eval"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_successor_shift"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_polePolynomial_successor_shift"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_polePolynomial_add_two_shift"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_shifted_as_actual_numerator"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_connectionRemainder_shifted_as_actual_numerator
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_connectionRemainder_shifted_as_actual_numerator
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_connectionRemainder_shifted_as_actual_numerator"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_eval_two"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_connectionRemainder_eval_two
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_connectionRemainder_eval_two
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_connectionRemainder_eval_two"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_connection_transport_positive"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_actual_chosen_connection_transport_positive
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_actual_chosen_connection_transport_positive
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_actual_chosen_connection_transport_positive"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.three_denominator_combination"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_three_denominator_combination
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_three_denominator_combination
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_three_denominator_combination"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport_eval"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport_eval
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport_eval
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport_eval"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
  do
    let wanted := "ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport"
    let found := (← getEnv).constants.toList.filter fun (n, _) =>
      n.toString == wanted || n.toString.endsWith ("." ++ wanted)
    unless found.length == 1 do throwError "Original complete type resolution failed"
    let (name, original) := found.head!
    let expected ← getConstInfo `NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport
    unless ← isDefEq original.type expected.type do throwError "Whole forall type differs {name}"
    let axs ← collectAxioms `NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard whole type endpoint"
    IO.println (Json.mkObj [("kind",Json.str "whole_forall_type_kernel"),
      ("original",Json.str name.toString),("expected",Json.str "NumeratorsIndependentWholeTypes.expected_actual_chosen_cleared_numerator_transport"),
      ("original_full_type_expr",Json.str (reprStr original.type)),
      ("expected_full_type_expr",Json.str (reprStr expected.type)),("axioms",toJson (axs.toList.map Name.toString))]).compress
