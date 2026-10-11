import Solutions.Sol_ZetaNine_CoefficientMapTelescoper_actual_polynomial_quotient_degree_bound
import Lean
open Polynomial Finset
open ZetaNine.CoefficientMapTelescoper ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapAggregate
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
namespace TelIndependent
theorem nonconstantCumulative : prefixSum (fun i => (i : ℚ) + 1) 2 = 6 := by
  norm_num [prefixSum, Finset.sum_range_succ]
theorem zeroNNumerator (W : ℚ[X]) : telescoperNumerator 0 W = 0 := by
  simp [telescoperNumerator]
theorem zeroMultiplierNumerator (n : ℕ) : telescoperNumerator n 0 = 0 := by
  simp [telescoperNumerator, cumulativeCoefficient, prefixSum,
    weightedLocalCoefficient, weightedClearedSeries]
theorem rootNodePositiveEdge (n : ℕ) :
    rootNode n (.inl ⟨n, by omega⟩) = (n : ℚ) + 1 := rfl
theorem rootNodeNegativeEdge (n : ℕ) :
    rootNode n (.inr ⟨n, by omega⟩) = -2 * (n : ℚ) := by
  simp [rootNode]
  ring
theorem oddNOneNodeProduct : rootPolynomial 1 =
    ((X - 1) * (X - 2)) * ((X + 1) * (X + 2)) := by
  rw [rootPolynomial_eq_explicit_products]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero]
  norm_num only [Nat.cast_ofNat, map_zero, map_one, map_ofNat, zero_add, add_zero, mul_one, one_mul]
  ring
theorem oddNOneNumeratorDegreeAllW (W : ℚ[X]) : (telescoperNumerator 1 W).natDegree ≤ 8 := by
  simpa using telescoperNumerator_natDegree_le 1 (by omega) W
theorem evenNTwoActualQuotient (W : ℚ[X]) (hstrong : StrongProperMultiplier 2 W)
    (hz : aggregate 2 W = 0) : ∃ H : ℚ[X],
    telescoperNumerator 2 W = rootPolynomial 2 * H ∧ H.natDegree ≤ 11 := by
  simpa using checked_actual_polynomial_quotient_degree_bound 2 (by omega)
    (by norm_num : Even 2) W hstrong hz
end TelIndependent
set_option pp.fullNames true
run_meta do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `TelIndependent do continue
    let .thmInfo _ := ci | continue
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration",Lean.Json.str name.toString),
      ("type",Lean.Json.str typ.pretty),("axioms",Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
