import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators
import Lean

/-! Independent review controls, PURE PREPARATION and UNCOMPILED.
They use the actual final source. No result is asserted until genuine Lean
execution and its source/log/exit/object bindings are recorded after lane grant. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapFormalTransportNumerators CoefficientMapParameterShift
open CoefficientMapKernelBridge CoefficientMapInjectivity CoefficientMapPartialFractions

namespace NumeratorsIndependentBoundaries

/-- n=1 is odd: no parity premise is allowed in the actual clear endpoint. -/
theorem first_chosen_full_numerator (r : Fin 5) :
    weightedNumerator 3 (X ^ r.val) =
      X ^ 9 * (X + C (3 : ℚ)) ^ 9 *
        (weightedNumerator 1 (connectionP 1 r)).comp (X + 1) +
      (X + C (3 : ℚ)) ^ 9 * shiftedRemainderNumerator 1 (connectionQ 1 r) -
      X ^ 9 * (shiftedRemainderNumerator 1 (connectionQ 1 r)).comp (X + 1) := by
  simpa only [Nat.reduceAdd, Nat.cast_one, show (1 : ℚ) + 2 = 3 by norm_num]
    using actual_chosen_cleared_numerator_transport 1 (by omega) r

theorem first_chosen_actual_difference (r : Fin 5) :
    CoefficientMap.weightedR 3 (X ^ r.val) (1 / 2 : ℚ) =
      CoefficientMap.weightedR 1 (connectionP 1 r) (3 / 2 : ℚ) +
        (connectionRemainder 1 (connectionQ 1 r) (3 / 2 : ℚ) -
          connectionRemainder 1 (connectionQ 1 r) (5 / 2 : ℚ)) := by
  convert actual_chosen_connection_transport_positive 1 (by omega) r (1 / 2) (by norm_num)
    using 1 <;> norm_num

theorem first_remainder_at_two_arbitrary_polynomial (q : ℚ[X]) :
    connectionRemainder 1 q 2 = 0 :=
  connectionRemainder_eval_two 1 (by omega) q

theorem first_remainder_at_two_degree_nine : connectionRemainder 1 (X ^ 9) 2 = 0 :=
  first_remainder_at_two_arbitrary_polynomial (X ^ 9)

theorem first_shifted_true_PF_numerator (q : ℚ[X]) :
    connectionRemainder 1 q 2 =
      (shiftedRemainderNumerator 1 q).eval 1 / (polePolynomial 2).eval 1 ^ 9 := by
  simpa only [Nat.reduceAdd, show (1 : ℚ) + 1 = 2 by norm_num]
    using connectionRemainder_shifted_as_actual_numerator 1 q 1 (by
      intro k hk
      exact ne_of_gt (by positivity))

/-- Degree is unnecessary for Q(2)=0 itself; it is needed for generic PF. -/
theorem all_positive_n_high_degree_zero (n : ℕ) (hn : 1 ≤ n) :
    connectionRemainder n (X ^ 100) 2 = 0 :=
  connectionRemainder_eval_two n hn (X ^ 100)

/-- Source pole-product statements retain m=0 even though chosen transport does not. -/
theorem zeroth_exact_pole_product : polePolynomial 2 =
    X * (polePolynomial 0).comp (X + 1) * (X + C (2 : ℚ)) := by
  simpa only [Nat.reduceAdd, Nat.cast_zero, zero_add]
    using polePolynomial_add_two_shift 0

theorem zeroth_shifted_actual_numerator (q : ℚ[X]) :
    connectionRemainder 0 q 2 =
      (shiftedRemainderNumerator 0 q).eval 1 / (polePolynomial 1).eval 1 ^ 9 := by
  simpa only [Nat.reduceAdd, show (1 : ℚ) + 1 = 2 by norm_num]
    using connectionRemainder_shifted_as_actual_numerator 0 q 1 (by
      intro k hk
      exact ne_of_gt (by positivity))

/-- Actual negative control: Q(2)=0 cannot be extended to n=0. -/
theorem zeroth_remainder_is_nonzero : connectionRemainder 0 (1 : ℚ[X]) 2 = 1 / 512 := by
  rw [connectionRemainder_as_actual_numerator 0 1 2 (by norm_num) (by
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    norm_num)]
  norm_num [remainderNumerator, polePolynomial]

/-- The n=1 zero must come from Q's extra factor, not from R_1(2). -/
theorem first_base_value_at_two_is_nonzero :
    CoefficientMap.weightedR 1 (1 : ℚ[X]) 2 = 1 / 2519424 := by
  rw [actual_weighted_rational_representation]
  norm_num [weightedNumerator, baseNumerator, polePolynomial]

theorem first_true_remainder_numerator_zero (q : ℚ[X]) :
    (remainderNumerator 1 q).eval 2 = 0 :=
  remainderNumerator_eval_two 1 (by omega) q

end NumeratorsIndependentBoundaries

open Lean Meta
run_meta do
  let names := (← getEnv).constants.toList.filterMap fun (name, ci) =>
    if name.getPrefix == `NumeratorsIndependentBoundaries then
      match ci with | .thmInfo _ => some name | _ => none
    else none
  unless names.length == 11 do throwError "Expected eleven actual independent boundaries"
  for name in names do
    let info ← getConstInfo name
    let axs ← collectAxioms name
    unless axs.toList.all (fun a => [`propext, `Classical.choice, `Quot.sound].contains a) do
      throwError "Nonstandard boundary proof axiom {name}"
    IO.println (Json.mkObj [("kind",Json.str "actual_independent_boundary"),
      ("declaration",Json.str name.toString),("whole_type_expr",Json.str (reprStr info.type)),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
