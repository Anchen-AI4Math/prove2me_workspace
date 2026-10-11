import missions.zeta9.formalization.CoefficientMapConnection
import Lean

noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace ConnectionBoundary

theorem n_one_local_coordinate : connectionV 1 = (X : ℚ[X]) ^ 2 := by
  norm_num [connectionV]
  ring

theorem n_one_actual_kernel (P q : ℚ[X]) (hq : q.natDegree ≤ 9)
    (heq : connectionD 1 * P.comp (connectionU 1) + connectionH 1 q = 0) :
    P = 0 ∧ q = 0 := connection_homogeneous_kernel_zero 1 (by norm_num) P q hq heq

theorem constant_q_forced_zero (n : ℕ) (hn : 1 ≤ n) (P : ℚ[X]) (a : ℚ)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n (C a) = 0) : a = 0 := by
  have h := connection_homogeneous_q_zero n hn P (C a) (by simp) heq
  exact C_eq_zero.mp h

theorem n_zero_nat_coordinate_truncated :
    connectionV 0 = (X : ℚ[X]) ^ 2 ∧ connectionV 0 ≠ X * (X - 1) := by
  have h : connectionV 0 = (X : ℚ[X]) ^ 2 := by
    norm_num [connectionV]
    ring
  refine ⟨h, ?_⟩
  intro heq
  have h1 := congrArg (fun p : ℚ[X] => p.coeff 1) heq
  norm_num [connectionV, coeff_X_mul] at h1

/-- This uses the written rational n-1=-1 coordinate, not Nat.sub at n=0. -/
theorem written_n_zero_nonzero_kernel :
    (X : ℚ[X]) ^ 9 ≠ 0 ∧
      (X - 1) * (X + 1) ^ 10 * (X ^ 9).comp (X * (X - 1)) -
        (X + 1) * (X - 1) ^ 10 * (X ^ 9).comp ((X + 1) * X) = 0 := by
  constructor
  · exact pow_ne_zero _ X_ne_zero
  · simp only [pow_comp, X_comp]
    ring

theorem first_factor_exact_value (n : ℕ) :
    ((X - C ((n : ℚ) + 1)) * (X + C ((n : ℚ) + 1)) ^ 10).eval 1 =
      -(n : ℚ) * ((n : ℚ) + 2) ^ 10 := by
  simp only [eval_mul, eval_sub, eval_add, eval_X, eval_C, eval_pow]
  ring

theorem simple_composition_at_n_one (q : ℚ[X]) (hq : q ≠ 0) :
    (q.comp (X ^ 2)).rootMultiplicity 1 = q.rootMultiplicity 1 := by
  apply rootMultiplicity_simple_composition q (X ^ 2) (X + 1) 1 1 hq
  · norm_num
    ring
  · norm_num

theorem actual_H_degree_fourteen_in_u (n : ℕ) (hn : 1 ≤ n) (q : ℚ[X])
    (hq : q.natDegree ≤ 9) : (connectionH n q).natDegree ≤ 28 := by
  have hd : (connectionH n q).natDegree ≤ 29 := by
    simpa [connectionOperator] using connectionOperator_degree n 0 q (by simp) hq
  by_cases h0 : connectionH n q = 0
  · simp [h0]
  obtain ⟨k, hk⟩ := reflected_natDegree_even n (connectionH n q) h0
    (connectionH_reflection n hn q)
  omega

theorem zero_rhs_unique (n : ℕ) (hn : 1 ≤ n) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 = 0 := by
  simpa using connection_original_system_exists_unique n hn 0 (by simp)

theorem n_one_fifth_original_target :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 1 * pq.1.comp (connectionU 1) + connectionH 1 pq.2 =
        (connectionTarget 1 4).comp (connectionU 1) :=
  connection_five_systems_unique 1 (by norm_num) ⟨4, by norm_num⟩

theorem original_even_parameter_targets (n : ℕ) (hn : 2 ≤ n) (_heven : Even n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) :=
  connection_five_systems_unique n (by omega) r

theorem reflected_zero_vector_kernel (n : ℕ) (hn : 1 ≤ n) (c : Fin 15 → ℚ)
    (hc : connectionLinearMap n c = 0) : c = 0 := by
  exact connectionLinearMap_injective n hn (hc.trans (map_zero _).symm)

end ConnectionBoundary

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true

run_meta do
  let names := [`ConnectionBoundary.n_one_local_coordinate,
    `ConnectionBoundary.n_one_actual_kernel, `ConnectionBoundary.constant_q_forced_zero,
    `ConnectionBoundary.n_zero_nat_coordinate_truncated,
    `ConnectionBoundary.written_n_zero_nonzero_kernel, `ConnectionBoundary.first_factor_exact_value,
    `ConnectionBoundary.simple_composition_at_n_one,
    `ConnectionBoundary.actual_H_degree_fourteen_in_u, `ConnectionBoundary.zero_rhs_unique,
    `ConnectionBoundary.n_one_fifth_original_target,
    `ConnectionBoundary.original_even_parameter_targets, `ConnectionBoundary.reflected_zero_vector_kernel]
  for name in names do
    let ci ← Lean.getConstInfo name
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration",Lean.Json.str name.toString),
      ("type",Lean.Json.str typ.pretty),("type_expression_repr",Lean.Json.str (reprStr ci.type)),
      ("axioms",Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
