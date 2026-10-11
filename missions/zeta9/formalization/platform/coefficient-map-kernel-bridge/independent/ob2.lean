import Solutions.Sol_ZetaNine_CoefficientMapKernelBridge_inverseMultiplier_actual_HasSum_and_absolute
import Lean
open Polynomial Finset
open ZetaNine.CoefficientMapAggregate ZetaNine.CoefficientMapFiniteSum
open ZetaNine.CoefficientMapKernelBridge ZetaNine.CoefficientMapSummation
namespace KernelIndependentOwn

def pureNine : Fin 5 → ℚ := fun i => if i = 4 then 1 else 0

theorem outputOrderB (n : ℕ) (W : ℚ[X]) : aggregate n W 0 = constantTerm n W := rfl

theorem outputOrderNine (n : ℕ) (W : ℚ[X]) : aggregate n W 4 = rho n 9 W := rfl

theorem zeroInverse (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) : inverseMultiplier n hn2 hn 0 = 0 := by
  exact (inverseMultiplier_unique n hn2 hn 0 0 (by simp) (aggregateLinearMap n).map_zero).symm

theorem rationalInverseQuartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) (b : Fin 5 → ℚ) :
    (inverseMultiplier n hn2 hn b).natDegree ≤ 4 := inverseMultiplier_natDegree_le n hn2 hn b

theorem pureNineNonzero : pureNine ≠ 0 := by
  intro h
  have v := congrFun h (4 : Fin 5)
  norm_num [pureNine] at v

theorem pureNineL : prescribedL pureNine = zetaReal 9 := by
  have h0 : pureNine (0 : Fin 5) = 0 := by decide
  have h1 : pureNine (1 : Fin 5) = 0 := by decide
  have h2 : pureNine (2 : Fin 5) = 0 := by decide
  have h3 : pureNine (3 : Fin 5) = 0 := by decide
  have h4 : pureNine (4 : Fin 5) = 1 := by decide
  simp [prescribedL, h0, h1, h2, h3, h4]

theorem pureNineActualCoefficient (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    rho n 9 (inverseMultiplier n hn2 hn pureNine) = 1 := by
  have h := congrFun (inverseMultiplier_actual_aggregate n hn2 hn pureNine) (4 : Fin 5)
  simpa [aggregate, pureNine] using h

theorem pureNineRealHasSum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n) :
    HasSum (fun k : ℕ => (ZetaNine.CoefficientMap.weightedR n (inverseMultiplier n hn2 hn pureNine)
      ((k + 1 : ℕ) : ℚ) : ℝ)) (zetaReal 9) := by
  have h := (checked_inverseMultiplier_actual_HasSum_and_absolute n hn2 hn pureNine).1
  simpa only [pureNineL] using h

end KernelIndependentOwn
set_option pp.fullNames true
run_meta do
  let env ← Lean.getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `KernelIndependentOwn do continue
    let .thmInfo _ := ci | continue
    let typ ← Lean.Meta.ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Lean.Json.mkObj [("declaration",Lean.Json.str name.toString),
      ("type",Lean.Json.str typ.pretty),("axioms",Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
