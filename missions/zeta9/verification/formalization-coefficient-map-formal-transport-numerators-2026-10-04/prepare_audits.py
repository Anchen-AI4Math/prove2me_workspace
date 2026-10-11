from run_author import *

prefix = 'import missions.zeta9.formalization.CoefficientMapFormalTransportNumerators\nimport Lean\n'
write(OUT/'source-full-audit.lean', prefix + '''
open Lean Meta
run_meta do
  let names := (← getEnv).constants.toList.filterMap fun (name, ci) =>
    if name.getPrefix == `ZetaNine.CoefficientMapFormalTransportNumerators ||
        name.toString.endsWith "ZetaNine.CoefficientMapFormalTransportNumerators.three_denominator_combination" then
      match ci with | .thmInfo _ => some name | _ => none
    else none
  unless names.length == 15 do throwError "Expected all fifteen actual source theorems"
  for name in names do
    let ci ← getConstInfo name
    let axioms ← collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("full_type_expression_repr", Json.str (reprStr ci.type)),
      ("axioms", toJson (axioms.toList.map Name.toString))]).compress
''')
write(OUT/'endpoint-audit.lean', prefix + '''
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Polynomial
namespace NumeratorTransportAuthorEndpoints
open ZetaNine CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapFormalTransportNumerators CoefficientMapKernelBridge
open CoefficientMapParameterShift
open CoefficientMapInjectivity CoefficientMapPartialFractions
theorem actual_clear_full_type : ∀ (n : Nat), 1 ≤ n → ∀ r : Fin 5,
    weightedNumerator (n + 2) (X ^ r.val) =
      X ^ 9 * (X + C ((n : Rat) + 2)) ^ 9 *
        (weightedNumerator n (connectionP n r)).comp (X + 1) +
      (X + C ((n : Rat) + 2)) ^ 9 * shiftedRemainderNumerator n (connectionQ n r) -
      X ^ 9 * (shiftedRemainderNumerator n (connectionQ n r)).comp (X + 1) :=
  actual_chosen_cleared_numerator_transport
theorem actual_difference_full_type : ∀ (n : Nat), 1 ≤ n → ∀ (r : Fin 5) (x : Rat), 0 < x →
    CoefficientMap.weightedR (n + 2) (X ^ r.val) x =
      CoefficientMap.weightedR n (connectionP n r) (x + 1) +
        (connectionRemainder n (connectionQ n r) (x + 1) -
          connectionRemainder n (connectionQ n r) (x + 1 + 1)) :=
  actual_chosen_connection_transport_positive
theorem actual_remainder_full_type : ∀ (n : Nat) (q : Rat[X]) (t : Rat),
    t - 1 ≠ 0 → (∀ k ≤ n, t + (k : Rat) ≠ 0) →
    connectionRemainder n q t = (remainderNumerator n q).eval t /
      ((t - 1) * (polePolynomial n).eval t) ^ 9 :=
  connectionRemainder_as_actual_numerator
theorem actual_shifted_remainder_full_type : ∀ (n : Nat) (q : Rat[X]) (x : Rat),
    (∀ k ≤ n + 1, x + (k : Rat) ≠ 0) →
    connectionRemainder n q (x + 1) =
      (shiftedRemainderNumerator n q).eval x / (polePolynomial (n + 1)).eval x ^ 9 :=
  connectionRemainder_shifted_as_actual_numerator
theorem actual_zero_full_type : ∀ (n : Nat), 1 ≤ n → ∀ q : Rat[X],
    connectionRemainder n q 2 = 0 := connectionRemainder_eval_two
theorem true_pole_shift_full_type : ∀ n : Nat,
    polePolynomial (n + 2) =
      X * (polePolynomial n).comp (X + 1) * (X + C ((n : Rat) + 2)) :=
  polePolynomial_add_two_shift
theorem n_one_chosen_clear (r : Fin 5) :
    weightedNumerator 3 (X ^ r.val) =
      X ^ 9 * (X + C (3 : Rat)) ^ 9 *
        (weightedNumerator 1 (connectionP 1 r)).comp (X + 1) +
      (X + C (3 : Rat)) ^ 9 * shiftedRemainderNumerator 1 (connectionQ 1 r) -
      X ^ 9 * (shiftedRemainderNumerator 1 (connectionQ 1 r)).comp (X + 1) := by
  simpa only [Nat.reduceAdd, Nat.cast_one, show (1 : Rat) + 2 = 3 by norm_num]
    using actual_chosen_cleared_numerator_transport 1 (by omega) r
theorem n_one_actual_zero (q : Rat[X]) : connectionRemainder 1 q 2 = 0 :=
  connectionRemainder_eval_two 1 (by omega) q
theorem n_zero_true_pole_shift : polePolynomial 2 =
    X * (polePolynomial 0).comp (X + 1) * (X + C (2 : Rat)) := by
  simpa only [Nat.reduceAdd, Nat.cast_zero, zero_add] using polePolynomial_add_two_shift 0
theorem n_one_shifted_remainder_boundary (q : Rat[X]) :
    connectionRemainder 1 q 2 = (shiftedRemainderNumerator 1 q).eval 1 /
      (polePolynomial 2).eval 1 ^ 9 := by
  simpa only [Nat.reduceAdd, show (1 : Rat) + 1 = 2 by norm_num]
    using connectionRemainder_shifted_as_actual_numerator 1 q 1 (by
    intro k hk; exact ne_of_gt (by positivity))
end NumeratorTransportAuthorEndpoints
open Lean Meta
run_meta do
  for (original, endpoint) in [
      (`ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_cleared_numerator_transport,
        `NumeratorTransportAuthorEndpoints.actual_clear_full_type),
      (`ZetaNine.CoefficientMapFormalTransportNumerators.actual_chosen_connection_transport_positive,
        `NumeratorTransportAuthorEndpoints.actual_difference_full_type),
      (`ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_as_actual_numerator,
        `NumeratorTransportAuthorEndpoints.actual_remainder_full_type),
      (`ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_shifted_as_actual_numerator,
        `NumeratorTransportAuthorEndpoints.actual_shifted_remainder_full_type),
      (`ZetaNine.CoefficientMapFormalTransportNumerators.connectionRemainder_eval_two,
        `NumeratorTransportAuthorEndpoints.actual_zero_full_type),
      (`ZetaNine.CoefficientMapFormalTransportNumerators.polePolynomial_add_two_shift,
        `NumeratorTransportAuthorEndpoints.true_pole_shift_full_type)] do
    let a ← getConstInfo original
    let b ← getConstInfo endpoint
    unless ← isDefEq a.type b.type do throwError "Whole original endpoint type mismatch {original}"
    IO.println (Json.mkObj [("whole_type_kernel_equal", Json.bool true),
      ("original", Json.str original.toString), ("endpoint", Json.str endpoint.toString)]).compress
  for (name, ci) in (← getEnv).constants.toList do
    unless name.getPrefix == `NumeratorTransportAuthorEndpoints do continue
    let .thmInfo _ := ci | continue
    let axioms ← collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("full_type_expression_repr", Json.str (reprStr ci.type)),
      ("axioms", toJson (axioms.toList.map Name.toString))]).compress
''')
modules = load(OUT/'preparation-state.json')['parent_modules'] + [MODULE]
write(OUT/'resolver.lean', '''import Lean
open Lean
def main : IO Unit := do
  let path ← IO.getEnv "LEAN_PATH"
  IO.println ((Json.mkObj [("kind",Json.str "actual_search_path"),("LEAN_PATH",Json.str (path.getD ""))]).compress)
  for m in (''' + json.dumps(modules) + ''' : List String) do
    let p ← Lean.findOLean ((m.splitOn ".").foldl Name.str Name.anonymous)
    IO.println ((Json.mkObj [("kind",Json.str "actual_module_resolution"),
      ("module",Json.str m),("resolved_olean",Json.str p.toString)]).compress)
''')
print('Prepared complete fifteen-source audit, ten endpoints/boundaries, six whole-type comparisons and seventeen resolver probes')
