import missions.zeta9.formalization.CoefficientMapFormalTransportBounds
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial
namespace FormalTransportAuthorEndpoints
open ZetaNine CoefficientMapConnection CoefficientMapFormalTransportData CoefficientMapFormalTransportBounds
open CoefficientMapAggregate CoefficientMapInjectivity
theorem chosen_pair_full_type : ∀ (n : Nat), 1 ≤ n → ∀ r : Fin 5,
    (connectionP n r).natDegree ≤ 4 ∧ (connectionQ n r).natDegree ≤ 9 ∧
      connectionD n * (connectionP n r).comp (connectionU n) + connectionH n (connectionQ n r) =
        (connectionTarget n r.val).comp (connectionU n) := connectionPair_spec
theorem Gamma_recovery_full_type : ∀ (n : Nat), 1 ≤ n → ∀ r : Fin 5,
    coordinatePolynomial (connectionGamma n r) = connectionP n r := connectionGamma_restores_P
theorem actual_zero_at_two_full_type : ∀ (n : Nat), 1 ≤ n → ∀ q : Rat[X],
    (remainderNumerator n q).eval 2 = 0 := remainderNumerator_eval_two
theorem actual_shifted_degree_full_type : ∀ (n : Nat) (q : Rat[X]), q.natDegree ≤ 9 →
    (shiftedRemainderNumerator n q).natDegree ≤ 2 * n + 18 := shiftedRemainderNumerator_degree_nine_bound
theorem actual_strict_proper_full_type : ∀ (n : Nat), 1 ≤ n → ∀ q : Rat[X], q.natDegree ≤ 9 →
    (shiftedRemainderNumerator n q).natDegree < (polePolynomial (n + 1) ^ 9).natDegree :=
  shiftedRemainderNumerator_below_pole_degree
theorem original_n_one_zero_and_proper (q : Rat[X]) (hq : q.natDegree ≤ 9) :
    (remainderNumerator 1 q).eval 2 = 0 ∧ (shiftedRemainderNumerator 1 q).natDegree < 27 :=
  ⟨boundary_n_one_zero q,boundary_n_one_strict_proper q hq⟩
theorem n_zero_choice_is_data_convention (r : Fin 5) : connectionP 0 r = 0 ∧ connectionQ 0 r = 0 := by
  simp [connectionP,connectionQ,connectionPair]
theorem previous_index_zero_guard (n s : Nat) (q : Rat[X]) : previousRemainderCoefficient n 0 s q = 0 := rfl
theorem old_index_zero_guard (n s : Nat) (P : Rat[X]) : extendedOldCoefficient n 0 s P = 0 := by
  simp [extendedOldCoefficient]
end FormalTransportAuthorEndpoints
open Lean Meta
run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `FormalTransportAuthorEndpoints do continue
    let .thmInfo _ := ci | continue
    let axioms ← collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
