import missions.zeta9.formalization.CoefficientMapConnection
import Lean
noncomputable section
open Polynomial ZetaNine.CoefficientMapConnection
namespace ConnectionExpected
theorem fullLift (n : ℕ) (hn : 1 ≤ n) (f : ℚ[X]) (hdeg : f.natDegree ≤ 29)
    (href : f.comp (connectionReflection n) = f) :
    ∃! c : Fin 15 → ℚ, connectionOperator n (inputP c) (inputQ c) = f :=
  connection_reflected_target_exists_unique n hn f hdeg href
theorem originalSystem (n : ℕ) (hn : 1 ≤ n) (f : ℚ[X]) (hf : f.natDegree ≤ 14) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        f.comp (connectionU n) := connection_original_system_exists_unique n hn f hf
theorem fiveSystems (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    ∃! pq : ℚ[X] × ℚ[X], pq.1.natDegree ≤ 4 ∧ pq.2.natDegree ≤ 9 ∧
      connectionD n * pq.1.comp (connectionU n) + connectionH n pq.2 =
        (connectionTarget n r.val).comp (connectionU n) := connection_five_systems_unique n hn r
theorem bijective (n : ℕ) (hn : 1 ≤ n) : Function.Bijective (connectionLinearMap n) :=
  connectionLinearMap_bijective n hn
theorem kernel (n : ℕ) (hn : 1 ≤ n) (P q : ℚ[X]) (hq : q.natDegree ≤ 9)
    (heq : connectionD n * P.comp (connectionU n) + connectionH n q = 0) :
    P = 0 ∧ q = 0 := connection_homogeneous_kernel_zero n hn P q hq heq
end ConnectionExpected
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  let pairs := [(`ZetaNine.CoefficientMapConnection.connection_reflected_target_exists_unique, `ConnectionExpected.fullLift),
    (`ZetaNine.CoefficientMapConnection.connection_original_system_exists_unique, `ConnectionExpected.originalSystem),
    (`ZetaNine.CoefficientMapConnection.connection_five_systems_unique, `ConnectionExpected.fiveSystems),
    (`ZetaNine.CoefficientMapConnection.connectionLinearMap_bijective, `ConnectionExpected.bijective),
    (`ZetaNine.CoefficientMapConnection.connection_homogeneous_kernel_zero, `ConnectionExpected.kernel)]
  for (actual, expected) in pairs do
    let ai ← Lean.getConstInfo actual
    let ei ← Lean.getConstInfo expected
    let same ← Lean.Meta.isDefEq ai.type ei.type
    unless same do throwError "Exact endpoint type mismatch: {actual}"
    let axs ← Lean.collectAxioms expected
    let typ ← Lean.Meta.ppExpr ei.type
    IO.println (Lean.Json.mkObj [("actual", Lean.Json.str actual.toString),
      ("expected", Lean.Json.str expected.toString), ("actual_type_isDefEq_expected", Lean.toJson same),
      ("expected_type", Lean.Json.str typ.pretty), ("axioms", Lean.toJson (axs.toList.map Lean.Name.toString))]).compress
