import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import IndependentExprDagV3
import Lean
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
noncomputable section
open scoped BigOperators
open Finset Polynomial ZetaNine
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportNumerators
open ZetaNine.CoefficientMapNumeratorPartialFractions

-- Independently stated complete forall types; no author expected-header copy.
namespace JetsIndependentExpected

theorem pole_factor : ∀ (m j : ℕ), j ≤ m →
    polePolynomial m = (X + C (j : ℚ)) * clearedPolePolynomial m j :=
  ZetaNine.CoefficientMapFormalTransportJets.pole_factor

theorem pole_comp_shift_factor : ∀ (m j : ℕ), j ≤ m →
    (polePolynomial m).comp (shiftedVariable j) = X * shiftedClearedDenominator m j :=
  ZetaNine.CoefficientMapFormalTransportJets.pole_comp_shift_factor

theorem pole_upper : ∀ (m : ℕ),
    polePolynomial (m + 1) = polePolynomial m * (X + C ((m + 1 : ℕ) : ℚ)) :=
  ZetaNine.CoefficientMapFormalTransportJets.pole_upper

theorem upper_cleared_denominator : ∀ (m j : ℕ), j ≤ m →
    shiftedClearedDenominator (m + 1) j =
      shiftedClearedDenominator m j * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) :=
  ZetaNine.CoefficientMapFormalTransportJets.upper_cleared_denominator

theorem shift_successor_comp : ∀ (j : ℕ), 1 ≤ j →
    (X + 1 : ℚ[X]).comp (shiftedVariable j) = shiftedVariable (j - 1) :=
  ZetaNine.CoefficientMapFormalTransportJets.shift_successor_comp

theorem lower_cleared_denominator : ∀ (m j : ℕ), 1 ≤ j → j ≤ m + 1 →
    shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * shiftedClearedDenominator m (j - 1) :=
  ZetaNine.CoefficientMapFormalTransportJets.lower_cleared_denominator

theorem upper_whole_actual_series : ∀ (m j : ℕ) (A : ℚ[X]), j ≤ m →
    numeratorClearedSeries (m + 1) j ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      numeratorClearedSeries m j A :=
  ZetaNine.CoefficientMapFormalTransportJets.upper_whole_actual_series

theorem lower_whole_actual_series : ∀ (m j : ℕ) (A : ℚ[X]), 1 ≤ j → j ≤ m + 1 →
    numeratorClearedSeries (m + 1) j (X ^ 9 * A.comp (X + 1)) =
      numeratorClearedSeries m (j - 1) A :=
  ZetaNine.CoefficientMapFormalTransportJets.lower_whole_actual_series

theorem local_zero_of_shift_X_nine : ∀ (m j s : ℕ) (A : ℚ[X]),
    1 ≤ s → s ≤ 9 → (X : ℚ[X]) ^ 9 ∣ A.comp (shiftedVariable j) →
      numeratorLocalCoefficient m j s A = 0 :=
  ZetaNine.CoefficientMapFormalTransportJets.local_zero_of_shift_X_nine

theorem upper_all_actual_jets : ∀ (m j s : ℕ) (A : ℚ[X]),
    j ≤ m + 1 → 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient (m + 1) j s ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
        if j ≤ m then numeratorLocalCoefficient m j s A else 0 :=
  ZetaNine.CoefficientMapFormalTransportJets.upper_all_actual_jets

theorem lower_all_actual_jets : ∀ (m j s : ℕ) (A : ℚ[X]),
    j ≤ m + 1 → 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient (m + 1) j s (X ^ 9 * A.comp (X + 1)) =
        if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) s A :=
  ZetaNine.CoefficientMapFormalTransportJets.lower_all_actual_jets

theorem double_all_actual_jets : ∀ (n j s : ℕ) (A : ℚ[X]),
    j ≤ n + 2 → 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient (n + 2) j s
        (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
          if 1 ≤ j ∧ j ≤ n + 1 then numeratorLocalCoefficient n (j - 1) s A else 0 :=
  ZetaNine.CoefficientMapFormalTransportJets.double_all_actual_jets

theorem numeratorClearedSeries_add : ∀ (m j : ℕ) (A B : ℚ[X]),
    numeratorClearedSeries m j (A + B) =
      numeratorClearedSeries m j A + numeratorClearedSeries m j B :=
  ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_add

theorem numeratorClearedSeries_sub : ∀ (m j : ℕ) (A B : ℚ[X]),
    numeratorClearedSeries m j (A - B) =
      numeratorClearedSeries m j A - numeratorClearedSeries m j B :=
  ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_sub

theorem numeratorClearedSeries_smul : ∀ (m j : ℕ) (a : ℚ) (A : ℚ[X]),
    numeratorClearedSeries m j (a • A) = a • numeratorClearedSeries m j A :=
  ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_smul

theorem numeratorLocalCoefficient_add : ∀ (m j s : ℕ) (A B : ℚ[X]),
    numeratorLocalCoefficient m j s (A + B) =
      numeratorLocalCoefficient m j s A + numeratorLocalCoefficient m j s B :=
  ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_add

theorem numeratorLocalCoefficient_smul : ∀ (m j s : ℕ) (a : ℚ) (A : ℚ[X]),
    numeratorLocalCoefficient m j s (a • A) = a * numeratorLocalCoefficient m j s A :=
  ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_smul

theorem actual_chosen_all_local_coefficients_transport :
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin 5) (j s : ℕ),
      j ≤ n + 2 → 1 ≤ s → s ≤ 9 →
        weightedLocalCoefficient (n + 2) j s (X ^ r.val) =
          extendedOldCoefficient n j s (connectionP n r) +
          extendedRemainderCoefficient n j s (connectionQ n r) -
          previousRemainderCoefficient n j s (connectionQ n r) :=
  ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_local_coefficients_transport

theorem actual_chosen_left_boundary_coefficient :
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin 5) (s : ℕ), 1 ≤ s → s ≤ 9 →
      weightedLocalCoefficient (n + 2) 0 s (X ^ r.val) =
        remainderCoefficient n 0 s (connectionQ n r) :=
  ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_left_boundary_coefficient

theorem actual_chosen_right_boundary_coefficient :
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin 5) (s : ℕ), 1 ≤ s → s ≤ 9 →
      weightedLocalCoefficient (n + 2) (n + 2) s (X ^ r.val) =
        -remainderCoefficient n (n + 1) s (connectionQ n r) :=
  ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_right_boundary_coefficient

theorem sum_upper_zero_extension : ∀ (N : ℕ) (f : ℕ → ℚ),
    (∑ j ∈ range (N + 2), if j ≤ N then f j else 0) = ∑ j ∈ range (N + 1), f j :=
  ZetaNine.CoefficientMapFormalTransportJets.sum_upper_zero_extension

theorem sum_lower_zero_extension : ∀ (N : ℕ) (f : ℕ → ℚ),
    (∑ j ∈ range (N + 2), if j = 0 then 0 else f (j - 1)) = ∑ j ∈ range (N + 1), f j :=
  ZetaNine.CoefficientMapFormalTransportJets.sum_lower_zero_extension

theorem sum_extendedOldCoefficient : ∀ (n s : ℕ) (P : ℚ[X]),
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P) =
      CoefficientMapFiniteSum.rho n s P :=
  ZetaNine.CoefficientMapFormalTransportJets.sum_extendedOldCoefficient

theorem sum_extendedRemainderCoefficient : ∀ (n s : ℕ) (q : ℚ[X]),
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q :=
  ZetaNine.CoefficientMapFormalTransportJets.sum_extendedRemainderCoefficient

theorem sum_previousRemainderCoefficient : ∀ (n s : ℕ) (q : ℚ[X]),
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q :=
  ZetaNine.CoefficientMapFormalTransportJets.sum_previousRemainderCoefficient

theorem actual_chosen_all_rho_transport :
    ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin 5) (s : ℕ), 1 ≤ s → s ≤ 9 →
      CoefficientMapFiniteSum.rho (n + 2) s (X ^ r.val) =
        CoefficientMapFiniteSum.rho n s (connectionP n r) :=
  ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_rho_transport

end JetsIndependentExpected

open Lean Meta
run_meta do
  let names : List String := [
    "pole_factor", "pole_comp_shift_factor", "pole_upper", "upper_cleared_denominator",
    "shift_successor_comp", "lower_cleared_denominator", "upper_whole_actual_series",
    "lower_whole_actual_series", "local_zero_of_shift_X_nine", "upper_all_actual_jets",
    "lower_all_actual_jets", "double_all_actual_jets", "numeratorClearedSeries_add",
    "numeratorClearedSeries_sub", "numeratorClearedSeries_smul", "numeratorLocalCoefficient_add",
    "numeratorLocalCoefficient_smul", "actual_chosen_all_local_coefficients_transport",
    "actual_chosen_left_boundary_coefficient", "actual_chosen_right_boundary_coefficient",
    "sum_upper_zero_extension", "sum_lower_zero_extension", "sum_extendedOldCoefficient",
    "sum_extendedRemainderCoefficient", "sum_previousRemainderCoefficient",
    "actual_chosen_all_rho_transport"]
  for suffix in names do
    let actual := Name.str `ZetaNine.CoefficientMapFormalTransportJets suffix
    let expected := Name.str `JetsIndependentExpected suffix
    let .thmInfo a ← getConstInfo actual | throwError "Source is not a theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Expected is not a theorem: {expected}"
    unless !(a.type.hasMVar || a.type.hasFVar || a.value.hasMVar || a.value.hasFVar ||
        b.type.hasMVar || b.type.hasFVar || b.value.hasMVar || b.value.hasFVar) do
      throwError "Unclosed source/expected expression: {actual}"
    let same ← isDefEq a.type b.type
    unless same do throwError "Whole expected type differs: {actual}"
    let aa ← Lean.collectAxioms actual
    let ba ← Lean.collectAxioms expected
    for axs in [aa, ba] do
      unless axs.toList.all (fun n => ([`propext, `Classical.choice, `Quot.sound] : List Name).contains n) do
        throwError "Unexpected source/expected axiom: {actual}"
    let ad ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type a.value)
    let bd ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type b.value)
    let (actualTypeDecoded, actualValueDecoded) ← ofExcept (IndependentLosslessExprDagV1.decode ad)
    let (expectedTypeDecoded, expectedValueDecoded) ← ofExcept (IndependentLosslessExprDagV1.decode bd)
    let flags := [Expr.equal a.type actualTypeDecoded, Expr.equal a.value actualValueDecoded, Expr.equal b.type expectedTypeDecoded, Expr.equal b.value expectedValueDecoded]
    unless flags.all id do throwError "Incomplete type/proof DAG reconstruction: {actual}"
    IO.println (Json.mkObj [
      ("kind", Json.str "independent_whole_type_proof_DAG"),
      ("declaration", Json.str actual.toString), ("expected", Json.str expected.toString),
      ("type_kernel_equal", toJson same), ("closed", toJson true),
      ("source_axioms", toJson (aa.toList.map Name.toString)),
      ("expected_axioms", toJson (ba.toList.map Name.toString)),
      ("source_full_type_proof_DAG", ad), ("expected_full_type_proof_DAG", bd),
      ("four_complete_reconstructions", toJson flags)]).compress
