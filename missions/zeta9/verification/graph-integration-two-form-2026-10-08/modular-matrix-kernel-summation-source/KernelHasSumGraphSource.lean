import Definitions.Def_ZetaNine_CoefficientMapKernelBridge
import Theorems.Thm_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL
import Theorems.Thm_ZetaNine_CoefficientMapSummation_actualSeries_norm_summable

/-! Pure uncompiled SOURCE for the existing inverse-HasSum graph node.
The two dependencies prove actual series convergence and exact odd-zeta value.
All inverse degree and five-coordinate restoration steps have full bodies. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.GraphBridge.KernelGraph
open CoefficientMapAggregate CoefficientMapKernelBridge CoefficientMapInjectivity

theorem inverse_quartic_degree_le (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := by
  let c : Fin 5 → ℚ := (actualAggregateEquiv n hn2 hn).symm b
  change (coordinatePolynomial c).natDegree ≤ 4
  unfold coordinatePolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  have h : (C (c i) * X ^ i.val : ℚ[X]).natDegree ≤
      (C (c i) : ℚ[X]).natDegree + (X ^ i.val : ℚ[X]).natDegree := natDegree_mul_le
  simp only [natDegree_C, natDegree_X_pow, zero_add] at h
  exact h.trans (by have := i.isLt; omega)

theorem inverse_actual_aggregate (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    aggregate n (inverseMultiplier n hn2 hn b) = b := by
  change (actualAggregateEquiv n hn2 hn) ((actualAggregateEquiv n hn2 hn).symm b) = b
  exact (actualAggregateEquiv n hn2 hn).apply_symm_apply b

theorem inverse_actual_exactL (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    CoefficientMapSummation.exactL n (inverseMultiplier n hn2 hn b) = prescribedL b := by
  have h := inverse_actual_aggregate n hn2 hn b
  have hB : CoefficientMapFiniteSum.constantTerm n (inverseMultiplier n hn2 hn b) = b 0 := congrFun h 0
  have h3 : CoefficientMapFiniteSum.rho n 3 (inverseMultiplier n hn2 hn b) = b 1 := congrFun h 1
  have h5 : CoefficientMapFiniteSum.rho n 5 (inverseMultiplier n hn2 hn b) = b 2 := congrFun h 2
  have h7 : CoefficientMapFiniteSum.rho n 7 (inverseMultiplier n hn2 hn b) = b 3 := congrFun h 3
  have h9 : CoefficientMapFiniteSum.rho n 9 (inverseMultiplier n hn2 hn b) = b 4 := congrFun h 4
  simp only [CoefficientMapSummation.exactL, hB, h3, h5, h7, h9, prescribedL]

theorem inverse_actual_strong_proper (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    StrongProperMultiplier n (inverseMultiplier n hn2 hn b) := by
  have hdegree := inverse_quartic_degree_le n hn2 hn b
  unfold StrongProperMultiplier
  omega

end ZetaNine.GraphBridge.KernelGraph

namespace ZetaNine.CoefficientMapKernelBridge

theorem inverseMultiplier_actual_HasSum_and_absolute (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (b : Fin 5 → ℚ) :
    HasSum (fun t : ℕ => (CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)) (prescribedL b) ∧
    Summable (fun t : ℕ => ‖(CoefficientMap.weightedR n (inverseMultiplier n hn2 hn b)
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) := by
  have hstrong := GraphBridge.KernelGraph.inverse_actual_strong_proper n hn2 hn b
  constructor
  · have h := CoefficientMapSummation.actualSeries_hasSum_exactL n hn _ hstrong
    rw [GraphBridge.KernelGraph.inverse_actual_exactL n hn2 hn b] at h
    simpa only [CoefficientMapSummation.actualSeries] using h
  · simpa only [CoefficientMapSummation.actualSeries] using
      CoefficientMapSummation.actualSeries_norm_summable n _ hstrong

end ZetaNine.CoefficientMapKernelBridge
