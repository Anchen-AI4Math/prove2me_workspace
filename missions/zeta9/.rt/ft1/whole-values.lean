import missions.zeta9.formalization.CoefficientMapFormalTransportBounds
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace FormalTransportAuthorValues
open ZetaNine CoefficientMapConnection CoefficientMapFormalTransportData

theorem pair_value : connectionPair = fun (n : Nat) (r : Fin 5) =>
    if hn : 1 ≤ n then Classical.choose (connection_five_systems_unique n hn r).exists else (0, 0) := rfl
theorem P_value : connectionP = fun (n : Nat) (r : Fin 5) => (connectionPair n r).1 := rfl
theorem q_value : connectionQ = fun (n : Nat) (r : Fin 5) => (connectionPair n r).2 := rfl
theorem Gamma_value : connectionGamma = fun (n : Nat) (r l : Fin 5) => (connectionP n r).coeff l.val := rfl
theorem numerator_value : remainderNumerator = fun (n : Nat) (q : Rat[X]) =>
    C ((n.factorial : Rat) ^ 7) *
      (∏ i ∈ range n, (X - C ((i : Rat) + 2))) *
      (∏ i ∈ range n, (X + C ((n : Rat) + (i : Rat) + 1))) * q.comp (connectionV n) := rfl
theorem shifted_numerator_value : shiftedRemainderNumerator = fun (n : Nat) (q : Rat[X]) =>
    (remainderNumerator n q).comp (X + 1) := rfl
theorem cleared_series_value : numeratorClearedSeries = fun (m j : Nat) (A : Rat[X]) =>
    ((A.comp (CoefficientMapJet.shiftedVariable j) : Rat[X]) : PowerSeries Rat) *
      ((CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries Rat) ^ 9)⁻¹ := rfl
theorem local_value : numeratorLocalCoefficient = fun (m j s : Nat) (A : Rat[X]) =>
    PowerSeries.coeff (9 - s) (numeratorClearedSeries m j A) := rfl
theorem remainder_coefficient_value : remainderCoefficient = fun (n j s : Nat) (q : Rat[X]) =>
    numeratorLocalCoefficient (n + 1) j s (shiftedRemainderNumerator n q) := rfl
theorem extended_old_value : extendedOldCoefficient = fun (n j s : Nat) (P : Rat[X]) =>
    if 1 ≤ j ∧ j ≤ n + 1 then CoefficientMapJet.weightedLocalCoefficient n (j - 1) s P else 0 := rfl
theorem extended_remainder_value : extendedRemainderCoefficient = fun (n j s : Nat) (q : Rat[X]) =>
    if j ≤ n + 1 then remainderCoefficient n j s q else 0 := rfl
theorem previous_value : previousRemainderCoefficient = fun (n j s : Nat) (q : Rat[X]) =>
    if j = 0 then 0 else extendedRemainderCoefficient n (j - 1) s q := rfl
end FormalTransportAuthorValues
open Lean Meta
run_meta do
  let env ← getEnv
  for (name, ci) in env.constants.toList do
    unless name.getPrefix == `FormalTransportAuthorValues do continue
    let .thmInfo _ := ci | continue
    let axioms ← collectAxioms name
    IO.println (Json.mkObj [("declaration",Json.str name.toString),
      ("full_type_expression_repr",Json.str (reprStr ci.type)),
      ("axioms",toJson (axioms.toList.map Name.toString))]).compress
