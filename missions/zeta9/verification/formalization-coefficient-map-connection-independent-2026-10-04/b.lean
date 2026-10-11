import missions.zeta9.formalization.CoefficientMapConnection
import Lean

noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace ConnectionIndependent

theorem recoverP (c : Fin 15 → ℚ) (i : Fin 5) :
    (inputP c).coeff i.val = c ⟨i.val, by omega⟩ :=
  coefficientPolynomial_coeff 5 _ i

theorem recoverQ (c : Fin 15 → ℚ) (i : Fin 10) :
    (inputQ c).coeff i.val = c ⟨i.val + 5, by omega⟩ :=
  coefficientPolynomial_coeff 10 _ i

theorem recoverEdges (c : Fin 15 → ℚ) :
    (inputP c).coeff 4 = c ⟨4, by omega⟩ ∧
    (inputQ c).coeff 0 = c ⟨5, by omega⟩ ∧
    (inputQ c).coeff 9 = c ⟨14, by omega⟩ := by
  exact ⟨recoverP c ⟨4, by omega⟩,
    recoverQ c ⟨0, by omega⟩, recoverQ c ⟨9, by omega⟩⟩

theorem restoreAll (c : Fin 15 → ℚ) (hP : inputP c = 0) (hq : inputQ c = 0) :
    c = 0 := by
  funext i
  by_cases hi : i.val < 5
  · have h := recoverP c ⟨i.val, hi⟩
    change (inputP c).coeff i.val = c i at h
    simpa [hP] using h.symm
  · have h := recoverQ c ⟨i.val - 5, by omega⟩
    have hi' : i.val - 5 + 5 = i.val := by omega
    change (inputQ c).coeff (i.val - 5) = c ⟨i.val - 5 + 5, _⟩ at h
    simpa [hq, hi'] using h.symm

theorem zeroInputs : inputP (0 : Fin 15 → ℚ) = 0 ∧ inputQ (0 : Fin 15 → ℚ) = 0 := by
  simp [inputP, inputQ, coefficientPolynomial]

theorem mixedInputs :
    (inputP (fun i : Fin 15 => (i.val + 1 : ℚ))).coeff 0 = 1 ∧
    (inputP (fun i : Fin 15 => (i.val + 1 : ℚ))).coeff 4 = 5 ∧
    (inputQ (fun i : Fin 15 => (i.val + 1 : ℚ))).coeff 0 = 6 ∧
    (inputQ (fun i : Fin 15 => (i.val + 1 : ℚ))).coeff 9 = 15 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := recoverP (fun i : Fin 15 => (i.val + 1 : ℚ)) ⟨0, by omega⟩
    norm_num at h
    exact h
  · have h := recoverP (fun i : Fin 15 => (i.val + 1 : ℚ)) ⟨4, by omega⟩
    norm_num at h
    exact h
  · have h := recoverQ (fun i : Fin 15 => (i.val + 1 : ℚ)) ⟨0, by omega⟩
    norm_num at h
    exact h
  · have h := recoverQ (fun i : Fin 15 => (i.val + 1 : ℚ)) ⟨9, by omega⟩
    norm_num at h
    exact h

theorem mixedDegree (n : ℕ) :
    (connectionOperator n (inputP (fun i : Fin 15 => (i.val + 1 : ℚ)))
      (inputQ (fun i : Fin 15 => (i.val + 1 : ℚ)))).natDegree ≤ 29 :=
  connectionOperator_degree n _ _ (coefficientPolynomial_degree 5 _)
    (coefficientPolynomial_degree 10 _)

theorem reflectedDegree28 (n : ℕ) (p : ℚ[X]) (hdeg : p.natDegree ≤ 29)
    (href : p.comp (connectionReflection n) = p) : p.natDegree ≤ 28 := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨k, hk⟩ := reflected_natDegree_even n p hp href
  omega

theorem actualDegree28 (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hP : P.natDegree ≤ 4) (hq : q.natDegree ≤ 9) :
    (connectionOperator n P q).natDegree ≤ 28 :=
  reflectedDegree28 n _ (connectionOperator_degree n P q hP hq)
    (connectionOperator_reflection n hn P q)

theorem affineReflectionAllowsOddCoefficient :
    (connectionU 3).comp (connectionReflection 3) = connectionU 3 ∧
      (connectionU 3).coeff 1 = 3 := by
  refine ⟨connectionU_reflection 3, ?_⟩
  norm_num [connectionU, coeff_X_mul]

theorem fullProjectedEquality (n : ℕ) (p f : ℚ[X])
    (hp : p.natDegree ≤ 29) (hf : f.natDegree ≤ 29)
    (hrp : p.comp (connectionReflection n) = p)
    (hrf : f.comp (connectionReflection n) = f)
    (hc : ∀ i : Fin 15, p.coeff (2 * i.val) = f.coeff (2 * i.val)) : p = f := by
  apply sub_eq_zero.mp
  apply reflected_even_coefficients_determine n
  · exact (natDegree_sub_le p f).trans (max_le hp hf)
  · simp only [sub_comp, hrp, hrf]
  · intro i
    rw [coeff_sub, hc i, sub_self]

theorem unrestrictedPKernel (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X])
    (hq : q.natDegree ≤ 9)
    (h : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := connection_homogeneous_kernel_zero n hn P q hq h

theorem zeroPAndQOperator (n : ℕ) : connectionOperator n 0 0 = 0 := by
  simp [connectionOperator, connectionH]

theorem zeroOriginalRHS (n : ℕ) (hn : 1 ≤ n) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 = 0 := by
  simpa using connection_original_system_exists_unique n hn 0 (by simp)

theorem mixedOriginalRHS (n : ℕ) (hn : 1 ≤ n) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (coefficientPolynomial 15 (fun i => (i.val + 1 : ℚ))).comp (connectionU n) :=
  connection_original_system_exists_unique n hn _ (coefficientPolynomial_degree 15 _)

theorem mixedTargetNonmonomial :
    (coefficientPolynomial 15 (fun i => (i.val + 1 : ℚ))).coeff 0 = 1 ∧
      (coefficientPolynomial 15 (fun i => (i.val + 1 : ℚ))).coeff 14 = 15 :=
  by
    constructor
    · have h := coefficientPolynomial_coeff 15 (fun i => (i.val + 1 : ℚ)) ⟨0, by omega⟩
      norm_num at h
      exact h
    · have h := coefficientPolynomial_coeff 15 (fun i => (i.val + 1 : ℚ)) ⟨14, by omega⟩
      norm_num at h
      exact h

theorem originalUniquenessAllPolynomials (n : ℕ) (hn : 1 ≤ n) (P Q q r : ℚ[X])
    (hq : q.natDegree ≤ 9) (hr : r.natDegree ≤ 9)
    (heq : connectionOperator n P q = connectionOperator n Q r) : P = Q ∧ q = r := by
  have hz : connectionOperator n (P - Q) (q - r) = 0 := by
    rw [connectionOperator_sub, heq, sub_self]
  obtain ⟨hp, hq'⟩ := connection_homogeneous_kernel_zero n hn _ _
    ((natDegree_sub_le _ _).trans (max_le hq hr)) hz
  exact ⟨sub_eq_zero.mp hp, sub_eq_zero.mp hq'⟩

theorem actualTargetFormula (n : ℕ) (r : Fin 5) :
    connectionTarget n r.val =
      C ((((n : ℚ) + 1) * ((n : ℚ) + 2)) ^ 7) *
      ((X - C (((n : ℚ) + 1) * (2 * (n : ℚ) + 1))) *
       (X - C (((n : ℚ) + 2) * (2 * (n : ℚ) + 2))) *
       (X - C (((n : ℚ) + 3) * (2 * (n : ℚ) + 3)))) *
      (X - C ((n : ℚ) + 1)) ^ r.val := rfl

theorem fiveTargetsAtOddNOne (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 1 * pq.1.comp (connectionU 1) + connectionH 1 pq.2 =
        (connectionTarget 1 r.val).comp (connectionU 1) :=
  connection_five_systems_unique 1 (by omega) r

theorem fiveTargetsAtEvenNTwo (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD 2 * pq.1.comp (connectionU 2) + connectionH 2 pq.2 =
        (connectionTarget 2 r.val).comp (connectionU 2) :=
  connection_five_systems_unique 2 (by omega) r

theorem nZeroCoordinateDistinction :
    connectionV 0 = (X : ℚ[X]) ^ 2 ∧ connectionV 0 ≠ X * (X - 1) := by
  have hv : connectionV 0 = (X : ℚ[X]) ^ 2 := by
    norm_num [connectionV]
    ring
  refine ⟨hv, ?_⟩
  intro heq
  have h := congrArg (fun p : ℚ[X] => p.coeff 1) heq
  norm_num [connectionV, coeff_X_mul] at h

theorem nZeroWrittenCoordinateKernel :
    (X : ℚ[X]) ^ 9 ≠ 0 ∧
      ((X : ℚ[X]) - 1) * (X + 1) ^ 10 * (X ^ 9 : ℚ[X]).comp (X * (X - 1)) -
        (X + 1) * (X - 1) ^ 10 * (X ^ 9 : ℚ[X]).comp ((X + 1) * X) = 0 := by
  constructor
  · exact pow_ne_zero _ X_ne_zero
  · simp only [pow_comp, X_comp]
    ring

theorem nZeroNatClipHNotWrittenKernel : connectionH 0 (X ^ 9) ≠ 0 := by
  intro hz
  have h := congrArg (fun p : ℚ[X] => p.eval 2) hz
  norm_num [connectionH, connectionV, eval_mul, eval_sub, eval_add, eval_pow,
    eval_comp, eval_X, eval_C] at h

end ConnectionIndependent

set_option pp.fullNames true
set_option pp.universes false
set_option pp.proofs true
run_meta do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `ConnectionIndependent do continue
    let .thmInfo _ := ci | continue
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration", Lean.Json.str name.toString),
      ("type", Lean.Json.str typ.pretty), ("type_expression_repr", Lean.Json.str (reprStr ci.type)),
      ("axioms", Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
