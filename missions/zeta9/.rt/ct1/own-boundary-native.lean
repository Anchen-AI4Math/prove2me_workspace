import missions.zeta9.formalization.CoefficientMapConnection
import Lean
set_option autoImplicit false
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace IndependentConnectionBoundary
theorem odd_five_kernel_no_P_degree (P q : Rat[X]) (hq : q.natDegree ≤ 9)
    (h : connectionD 5 * P.comp (connectionU 5) + connectionH 5 q = 0) : P = 0 ∧ q = 0 :=
  connection_homogeneous_kernel_zero 5 (by decide) P q hq h
theorem genuine_map_at_one_bijective : Function.Bijective (connectionLinearMap 1) :=
  connectionLinearMap_bijective 1 (by decide)
theorem first_positive_last_target : ∃! pq : Rat[X] × Rat[X],
    pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 1 * pq.1.comp (connectionU 1) + connectionH 1 pq.2 =
        (connectionTarget 1 4).comp (connectionU 1) :=
  connection_five_systems_unique 1 (by decide) (4 : Fin 5)
theorem first_P_input_coordinate (c : Fin 15 → Rat) : (inputP c).coeff 0 = c (0 : Fin 15) := by
  change (coefficientPolynomial 5 (fun i => c ⟨i.val, by omega⟩)).coeff (0 : Fin 5).val = _
  rw [coefficientPolynomial_coeff]
  rfl
theorem last_q_input_coordinate (c : Fin 15 → Rat) : (inputQ c).coeff 9 = c (14 : Fin 15) := by
  change (coefficientPolynomial 10 (fun i => c ⟨i.val + 5, by omega⟩)).coeff (9 : Fin 10).val = _
  rw [coefficientPolynomial_coeff]
  rfl
theorem last_even_output_coefficient (n : Nat) (c : Fin 15 → Rat) :
    connectionLinearMap n c (14 : Fin 15) =
      (connectionOperator n (inputP c) (inputQ c)).coeff 28 := rfl
theorem zero_q_unbounded_P (n : Nat) (hn : 1 ≤ n) (P : Rat[X])
    (h : connectionD n * P.comp (connectionU n) = 0) : P = 0 := by
  have hfull : connectionD n * P.comp (connectionU n) + connectionH n 0 = 0 := by
    simpa only [connectionH, zero_comp, mul_zero, sub_self, add_zero] using h
  exact (connection_homogeneous_kernel_zero n hn P 0 (by simp) hfull).1
theorem constant_q_coefficient_forced_zero (n : Nat) (hn : 1 ≤ n) (P : Rat[X]) (a : Rat)
    (h : connectionD n * P.comp (connectionU n) + connectionH n (C a) = 0) : a = 0 := by
  exact C_eq_zero.mp (connection_homogeneous_kernel_zero n hn P (C a) (by simp) h).2
end IndependentConnectionBoundary
open Lean Meta
run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `IndependentConnectionBoundary do continue
    let .thmInfo _ := ci | continue
    let ax ← collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (ax.toList.map Name.toString))]).compress
