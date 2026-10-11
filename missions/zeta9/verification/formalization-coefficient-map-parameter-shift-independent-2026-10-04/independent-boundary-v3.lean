import missions.zeta9.formalization.CoefficientMapParameterShift
import Lean

-- Independent real boundaries. Uncompiled preparation, not proof evidence.
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace IndependentParameterShiftBoundary
open ZetaNine
open CoefficientMapKernelBridge CoefficientMapConnection CoefficientMapParameterShift

theorem clipped_V_n0 : connectionV 0 = (X : Rat[X]) ^ 2 := by
  simp [connectionV, pow_two]

theorem V_n1 : connectionV 1 = (X : Rat[X]) ^ 2 := by
  simp [connectionV, pow_two]

theorem n0_successor_V_argument : (connectionV 0).eval (3 : Rat) = 9 := by
  norm_num [connectionV]

theorem n0_H_second_argument : ((3 : Rat) * (2 : Rat)) = 6 := by norm_num

theorem n0_t2_new_regular : ∀ k : Nat, k ≤ 2 → (2 : Rat) - 1 + (k : Rat) ≠ 0 := by
  intro k hk
  have hnonneg : (0 : Rat) ≤ (k : Rat) := Nat.cast_nonneg k
  linarith

theorem n0_Q_at_2 : connectionRemainder 0 (X : Rat[X]) (2 : Rat) = 1 / 128 := by
  norm_num [connectionRemainder, CoefficientMap.actualR, CoefficientMap.numerator,
    CoefficientMap.poleProduct, connectionV, Finset.prod_range_succ]

theorem n0_Q_at_3 : connectionRemainder 0 (X : Rat[X]) (3 : Rat) = 1 / 1119744 := by
  norm_num [connectionRemainder, CoefficientMap.actualR, CoefficientMap.numerator,
    CoefficientMap.poleProduct, connectionV, Finset.prod_range_succ]

theorem n0_Q_difference_value :
    connectionRemainder 0 (X : Rat[X]) (2 : Rat) -
      connectionRemainder 0 (X : Rat[X]) (3 : Rat) = 8747 / 1119744 := by
  rw [n0_Q_at_2, n0_Q_at_3]
  norm_num

theorem n0_R_H_over_D_value :
    CoefficientMap.actualR 0 (2 : Rat) * (connectionH 0 (X : Rat[X])).eval (2 : Rat) /
      (connectionD 0).eval (2 : Rat) = 13121 / 1679616 := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct,
    connectionH, connectionV, connectionD, connectionU, Finset.prod_range_succ]

theorem n0_clipped_V_Q_difference_counterexample :
    connectionRemainder 0 (X : Rat[X]) (2 : Rat) -
      connectionRemainder 0 (X : Rat[X]) (3 : Rat) ≠
    CoefficientMap.actualR 0 (2 : Rat) * (connectionH 0 (X : Rat[X])).eval (2 : Rat) /
      (connectionD 0).eval (2 : Rat) := by
  rw [n0_Q_difference_value, n0_R_H_over_D_value]
  norm_num

theorem independent_old_regular (n : Nat) (t : Rat)
    (h : ∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) :
    ∀ k ≤ n, t + (k : Rat) ≠ 0 := by
  intro k hk
  have h1 := h (k + 1) (by omega)
  convert h1 using 1 <;> push_cast <;> ring

theorem independent_old_successor_regular (n : Nat) (t : Rat)
    (h : ∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) :
    ∀ k ≤ n, t + 1 + (k : Rat) ≠ 0 := by
  intro k hk
  have h2 := h (k + 2) (by omega)
  convert h2 using 1 <;> push_cast <;> ring

theorem independent_required_denominators (n : Nat) (t : Rat)
    (h : ∀ k ≤ n + 2, t - 1 + (k : Rat) ≠ 0) :
    t - 1 ≠ 0 ∧ t ≠ 0 ∧ t + (n : Rat) + 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using h 0 (by omega)
  · convert h 1 (by omega) using 1 <;> norm_num <;> ring
  · convert h (n + 2) (by omega) using 1 <;> push_cast <;> ring

theorem n2_t2_new_regular : ∀ k : Nat, k ≤ 4 → (2 : Rat) - 1 + (k : Rat) ≠ 0 := by
  intro k hk
  have hnonneg : (0 : Rat) ≤ (k : Rat) := Nat.cast_nonneg k
  linarith

theorem n2_t2_old_R_zero : CoefficientMap.actualR 2 (2 : Rat) = 0 := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct,
    Finset.prod_range_succ]

theorem n2_t2_new_R_zero : CoefficientMap.actualR 4 (1 : Rat) = 0 := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct,
    Finset.prod_range_succ]

theorem n2_t2_D_nonzero : (connectionD 2).eval (2 : Rat) ≠ 0 := by
  norm_num [connectionD, connectionU]

theorem n2_t2_R_ratio_with_zero_old_R :
    CoefficientMap.actualR 4 (1 : Rat) * (connectionD 2).eval (2 : Rat) =
      parameterScale 2 * (connectionZ 2).eval (8 : Rat) * CoefficientMap.actualR 2 (2 : Rat) := by
  rw [n2_t2_old_R_zero, n2_t2_new_R_zero]
  simp

theorem n0_t2_R_ratio_still_valid :
    CoefficientMap.actualR 2 (1 : Rat) * (connectionD 0).eval (2 : Rat) =
      parameterScale 0 * (connectionZ 0).eval (4 : Rat) * CoefficientMap.actualR 0 (2 : Rat) := by
  norm_num [CoefficientMap.actualR, CoefficientMap.numerator, CoefficientMap.poleProduct,
    connectionD, connectionU, connectionZ, parameterScale, Finset.prod_range_succ]

theorem zero_q_remainder (n : Nat) (t : Rat) :
    connectionRemainder n (0 : Rat[X]) t = 0 := by simp [connectionRemainder]

theorem zero_q_difference (n : Nat) (t : Rat) :
    connectionRemainder n (0 : Rat[X]) t - connectionRemainder n (0 : Rat[X]) (t + 1) = 0 := by
  rw [zero_q_remainder, zero_q_remainder]
  ring

theorem all_positive_n_V_successor (n : Nat) (hn : 1 ≤ n) (t : Rat) :
    (connectionV n).eval (t + 1) = (t + 1) * (t + (n : Rat)) := by
  simp only [connectionV, eval_mul, eval_add, eval_X, eval_C, Nat.cast_sub hn, Nat.cast_one]
  ring

theorem t_one_is_excluded (n : Nat) :
    ¬ (∀ k ≤ n + 2, (1 : Rat) - 1 + (k : Rat) ≠ 0) := by
  intro h
  have h0 := h 0 (by omega)
  norm_num at h0

theorem t_zero_is_excluded (n : Nat) :
    ¬ (∀ k ≤ n + 2, (0 : Rat) - 1 + (k : Rat) ≠ 0) := by
  intro h
  have h1 := h 1 (by omega)
  norm_num at h1

theorem t_minus_n_minus_one_is_excluded (n : Nat) :
    ¬ (∀ k ≤ n + 2, (-(n : Rat) - 1) - 1 + (k : Rat) ≠ 0) := by
  intro h
  have hx := h (n + 2) (by omega)
  apply hx
  push_cast
  ring

theorem first_original_system_at_n1 :
    ∃! pq : Rat[X] × Rat[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 1 * pq.1.comp (connectionU 1) + connectionH 1 pq.2 =
        (connectionTarget 1 0).comp (connectionU 1) ∧
      ∀ t : Rat, (∀ k : Nat, k ≤ 3 → t - 1 + (k : Rat) ≠ 0) →
        CoefficientMap.actualR 3 (t - 1) * (t * (t + 1) - 2) ^ (0 : Nat) =
          CoefficientMap.actualR 1 t * pq.1.eval (t * (t + 1)) +
            (connectionRemainder 1 pq.2 t - connectionRemainder 1 pq.2 (t + 1)) := by
  simpa using five_actual_connection_transports_exist_unique 1 (by decide) (0 : Fin 5)

theorem last_original_system_at_n2 :
    ∃! pq : Rat[X] × Rat[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 2 * pq.1.comp (connectionU 2) + connectionH 2 pq.2 =
        (connectionTarget 2 4).comp (connectionU 2) ∧
      ∀ t : Rat, (∀ k : Nat, k ≤ 4 → t - 1 + (k : Rat) ≠ 0) →
        CoefficientMap.actualR 4 (t - 1) * (t * (t + 2) - 3) ^ (4 : Nat) =
          CoefficientMap.actualR 2 t * pq.1.eval (t * (t + 2)) +
            (connectionRemainder 2 pq.2 t - connectionRemainder 2 pq.2 (t + 1)) := by
  simpa using five_actual_connection_transports_exist_unique 2 (by decide) (4 : Fin 5)

end IndependentParameterShiftBoundary

open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for name in [`IndependentParameterShiftBoundary.clipped_V_n0,
    `IndependentParameterShiftBoundary.V_n1,
    `IndependentParameterShiftBoundary.n0_successor_V_argument,
    `IndependentParameterShiftBoundary.n0_H_second_argument,
    `IndependentParameterShiftBoundary.n0_t2_new_regular,
    `IndependentParameterShiftBoundary.n0_Q_at_2,
    `IndependentParameterShiftBoundary.n0_Q_at_3,
    `IndependentParameterShiftBoundary.n0_Q_difference_value,
    `IndependentParameterShiftBoundary.n0_R_H_over_D_value,
    `IndependentParameterShiftBoundary.n0_clipped_V_Q_difference_counterexample,
    `IndependentParameterShiftBoundary.independent_old_regular,
    `IndependentParameterShiftBoundary.independent_old_successor_regular,
    `IndependentParameterShiftBoundary.independent_required_denominators,
    `IndependentParameterShiftBoundary.n2_t2_new_regular,
    `IndependentParameterShiftBoundary.n2_t2_old_R_zero,
    `IndependentParameterShiftBoundary.n2_t2_new_R_zero,
    `IndependentParameterShiftBoundary.n2_t2_D_nonzero,
    `IndependentParameterShiftBoundary.n2_t2_R_ratio_with_zero_old_R,
    `IndependentParameterShiftBoundary.n0_t2_R_ratio_still_valid,
    `IndependentParameterShiftBoundary.zero_q_remainder,
    `IndependentParameterShiftBoundary.zero_q_difference,
    `IndependentParameterShiftBoundary.all_positive_n_V_successor,
    `IndependentParameterShiftBoundary.t_one_is_excluded,
    `IndependentParameterShiftBoundary.t_zero_is_excluded,
    `IndependentParameterShiftBoundary.t_minus_n_minus_one_is_excluded,
    `IndependentParameterShiftBoundary.first_original_system_at_n1,
    `IndependentParameterShiftBoundary.last_original_system_at_n2] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("type_pp_diagnostic",Json.str typ.pretty),
      ("axioms",toJson (axs.toList.map Name.toString))]).compress
