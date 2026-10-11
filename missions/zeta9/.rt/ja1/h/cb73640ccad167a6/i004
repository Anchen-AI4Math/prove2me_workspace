import missions.zeta9.formalization.CoefficientMapFormalTransportJets
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
open ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapFormalTransportNumerators
open ZetaNine.CoefficientMapNumeratorPartialFractions
open ZetaNine.CoefficientMapFormalTransportJets
namespace JetsAuthorExpected

theorem expected_pole_factor (m j : ℕ) (hj : j ≤ m) :
    polePolynomial m = (X + C (j : ℚ)) * clearedPolePolynomial m j := by
  exact ZetaNine.CoefficientMapFormalTransportJets.pole_factor m j hj

theorem expected_pole_comp_shift_factor (m j : ℕ) (hj : j ≤ m) :
    (polePolynomial m).comp (shiftedVariable j) = X * shiftedClearedDenominator m j := by
  exact ZetaNine.CoefficientMapFormalTransportJets.pole_comp_shift_factor m j hj

theorem expected_pole_upper (m : ℕ) :
    polePolynomial (m + 1) = polePolynomial m * (X + C ((m + 1 : ℕ) : ℚ)) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.pole_upper m

theorem expected_upper_cleared_denominator (m j : ℕ) (hj : j ≤ m) :
    shiftedClearedDenominator (m + 1) j =
      shiftedClearedDenominator m j * (shiftedVariable j + C ((m + 1 : ℕ) : ℚ)) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.upper_cleared_denominator m j hj

theorem expected_shift_successor_comp (j : ℕ) (hj : 1 ≤ j) :
    (X + 1 : ℚ[X]).comp (shiftedVariable j) = shiftedVariable (j - 1) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.shift_successor_comp j hj

theorem expected_lower_cleared_denominator (m j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    shiftedClearedDenominator (m + 1) j =
      shiftedVariable j * shiftedClearedDenominator m (j - 1) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.lower_cleared_denominator m j hj1 hj

theorem expected_upper_whole_actual_series (m j : ℕ) (A : ℚ[X]) (hj : j ≤ m) :
    numeratorClearedSeries (m + 1) j ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      numeratorClearedSeries m j A := by
  exact ZetaNine.CoefficientMapFormalTransportJets.upper_whole_actual_series m j A hj

theorem expected_lower_whole_actual_series (m j : ℕ) (A : ℚ[X])
    (hj1 : 1 ≤ j) (hj : j ≤ m + 1) :
    numeratorClearedSeries (m + 1) j (X ^ 9 * A.comp (X + 1)) =
      numeratorClearedSeries m (j - 1) A := by
  exact ZetaNine.CoefficientMapFormalTransportJets.lower_whole_actual_series m j A hj1 hj

theorem expected_local_zero_of_shift_X_nine (m j s : ℕ) (A : ℚ[X])
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9)
    (hA : (X : ℚ[X]) ^ 9 ∣ A.comp (shiftedVariable j)) :
    numeratorLocalCoefficient m j s A = 0 := by
  exact ZetaNine.CoefficientMapFormalTransportJets.local_zero_of_shift_X_nine m j s A hs1 hs9 hA

theorem expected_upper_all_actual_jets (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s ((X + C ((m + 1 : ℕ) : ℚ)) ^ 9 * A) =
      if j ≤ m then numeratorLocalCoefficient m j s A else 0 := by
  exact ZetaNine.CoefficientMapFormalTransportJets.upper_all_actual_jets m j s A hj hs1 hs9

theorem expected_lower_all_actual_jets (m j s : ℕ) (A : ℚ[X])
    (hj : j ≤ m + 1) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (m + 1) j s (X ^ 9 * A.comp (X + 1)) =
      if j = 0 then 0 else numeratorLocalCoefficient m (j - 1) s A := by
  exact ZetaNine.CoefficientMapFormalTransportJets.lower_all_actual_jets m j s A hj hs1 hs9

theorem expected_double_all_actual_jets (n j s : ℕ) (A : ℚ[X])
    (hj : j ≤ n + 2) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    numeratorLocalCoefficient (n + 2) j s
      (X ^ 9 * (X + C ((n : ℚ) + 2)) ^ 9 * A.comp (X + 1)) =
      if 1 ≤ j ∧ j ≤ n + 1 then numeratorLocalCoefficient n (j - 1) s A else 0 := by
  exact ZetaNine.CoefficientMapFormalTransportJets.double_all_actual_jets n j s A hj hs1 hs9

theorem expected_numeratorClearedSeries_add (m j : ℕ) (A B : ℚ[X]) :
    numeratorClearedSeries m j (A + B) =
      numeratorClearedSeries m j A + numeratorClearedSeries m j B := by
  exact ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_add m j A B

theorem expected_numeratorClearedSeries_sub (m j : ℕ) (A B : ℚ[X]) :
    numeratorClearedSeries m j (A - B) =
      numeratorClearedSeries m j A - numeratorClearedSeries m j B := by
  exact ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_sub m j A B

theorem expected_numeratorClearedSeries_smul (m j : ℕ) (a : ℚ) (A : ℚ[X]) :
    numeratorClearedSeries m j (a • A) = a • numeratorClearedSeries m j A := by
  exact ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_smul m j a A

theorem expected_numeratorLocalCoefficient_add (m j s : ℕ) (A B : ℚ[X]) :
    numeratorLocalCoefficient m j s (A + B) =
      numeratorLocalCoefficient m j s A + numeratorLocalCoefficient m j s B := by
  exact ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_add m j s A B

theorem expected_numeratorLocalCoefficient_smul (m j s : ℕ) (a : ℚ) (A : ℚ[X]) :
    numeratorLocalCoefficient m j s (a • A) = a * numeratorLocalCoefficient m j s A := by
  exact ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_smul m j s a A

theorem expected_actual_chosen_all_local_coefficients_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (j s : ℕ) (hj : j ≤ n + 2) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) j s (X ^ r.val) =
      extendedOldCoefficient n j s (connectionP n r) +
        extendedRemainderCoefficient n j s (connectionQ n r) -
        previousRemainderCoefficient n j s (connectionQ n r) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_local_coefficients_transport n hn r j s hj hs1 hs9

theorem expected_actual_chosen_left_boundary_coefficient (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) 0 s (X ^ r.val) =
      remainderCoefficient n 0 s (connectionQ n r) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_left_boundary_coefficient n hn r s hs1 hs9

theorem expected_actual_chosen_right_boundary_coefficient (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    weightedLocalCoefficient (n + 2) (n + 2) s (X ^ r.val) =
      -remainderCoefficient n (n + 1) s (connectionQ n r) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_right_boundary_coefficient n hn r s hs1 hs9

theorem expected_sum_upper_zero_extension (N : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range (N + 2), if j ≤ N then f j else 0) =
      ∑ j ∈ range (N + 1), f j := by
  exact ZetaNine.CoefficientMapFormalTransportJets.sum_upper_zero_extension N f

theorem expected_sum_lower_zero_extension (N : ℕ) (f : ℕ → ℚ) :
    (∑ j ∈ range (N + 2), if j = 0 then 0 else f (j - 1)) =
      ∑ j ∈ range (N + 1), f j := by
  exact ZetaNine.CoefficientMapFormalTransportJets.sum_lower_zero_extension N f

theorem expected_sum_extendedOldCoefficient (n s : ℕ) (P : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedOldCoefficient n j s P) =
      CoefficientMapFiniteSum.rho n s P := by
  exact ZetaNine.CoefficientMapFormalTransportJets.sum_extendedOldCoefficient n s P

theorem expected_sum_extendedRemainderCoefficient (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), extendedRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q := by
  exact ZetaNine.CoefficientMapFormalTransportJets.sum_extendedRemainderCoefficient n s q

theorem expected_sum_previousRemainderCoefficient (n s : ℕ) (q : ℚ[X]) :
    (∑ j ∈ range (n + 3), previousRemainderCoefficient n j s q) =
      ∑ j ∈ range (n + 2), remainderCoefficient n j s q := by
  exact ZetaNine.CoefficientMapFormalTransportJets.sum_previousRemainderCoefficient n s q

theorem expected_actual_chosen_all_rho_transport (n : ℕ) (hn : 1 ≤ n)
    (r : Fin 5) (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    CoefficientMapFiniteSum.rho (n + 2) s (X ^ r.val) =
      CoefficientMapFiniteSum.rho n s (connectionP n r) := by
  exact ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_rho_transport n hn r s hs1 hs9

end JetsAuthorExpected
open Lean Meta
set_option pp.fullNames true
set_option pp.proofs true
run_meta do
  for (actual,expected) in [(`ZetaNine.CoefficientMapFormalTransportJets.pole_factor, `JetsAuthorExpected.expected_pole_factor), (`ZetaNine.CoefficientMapFormalTransportJets.pole_comp_shift_factor, `JetsAuthorExpected.expected_pole_comp_shift_factor), (`ZetaNine.CoefficientMapFormalTransportJets.pole_upper, `JetsAuthorExpected.expected_pole_upper), (`ZetaNine.CoefficientMapFormalTransportJets.upper_cleared_denominator, `JetsAuthorExpected.expected_upper_cleared_denominator), (`ZetaNine.CoefficientMapFormalTransportJets.shift_successor_comp, `JetsAuthorExpected.expected_shift_successor_comp), (`ZetaNine.CoefficientMapFormalTransportJets.lower_cleared_denominator, `JetsAuthorExpected.expected_lower_cleared_denominator), (`ZetaNine.CoefficientMapFormalTransportJets.upper_whole_actual_series, `JetsAuthorExpected.expected_upper_whole_actual_series), (`ZetaNine.CoefficientMapFormalTransportJets.lower_whole_actual_series, `JetsAuthorExpected.expected_lower_whole_actual_series), (`ZetaNine.CoefficientMapFormalTransportJets.local_zero_of_shift_X_nine, `JetsAuthorExpected.expected_local_zero_of_shift_X_nine), (`ZetaNine.CoefficientMapFormalTransportJets.upper_all_actual_jets, `JetsAuthorExpected.expected_upper_all_actual_jets), (`ZetaNine.CoefficientMapFormalTransportJets.lower_all_actual_jets, `JetsAuthorExpected.expected_lower_all_actual_jets), (`ZetaNine.CoefficientMapFormalTransportJets.double_all_actual_jets, `JetsAuthorExpected.expected_double_all_actual_jets), (`ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_add, `JetsAuthorExpected.expected_numeratorClearedSeries_add), (`ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_sub, `JetsAuthorExpected.expected_numeratorClearedSeries_sub), (`ZetaNine.CoefficientMapFormalTransportJets.numeratorClearedSeries_smul, `JetsAuthorExpected.expected_numeratorClearedSeries_smul), (`ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_add, `JetsAuthorExpected.expected_numeratorLocalCoefficient_add), (`ZetaNine.CoefficientMapFormalTransportJets.numeratorLocalCoefficient_smul, `JetsAuthorExpected.expected_numeratorLocalCoefficient_smul), (`ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_local_coefficients_transport, `JetsAuthorExpected.expected_actual_chosen_all_local_coefficients_transport), (`ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_left_boundary_coefficient, `JetsAuthorExpected.expected_actual_chosen_left_boundary_coefficient), (`ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_right_boundary_coefficient, `JetsAuthorExpected.expected_actual_chosen_right_boundary_coefficient), (`ZetaNine.CoefficientMapFormalTransportJets.sum_upper_zero_extension, `JetsAuthorExpected.expected_sum_upper_zero_extension), (`ZetaNine.CoefficientMapFormalTransportJets.sum_lower_zero_extension, `JetsAuthorExpected.expected_sum_lower_zero_extension), (`ZetaNine.CoefficientMapFormalTransportJets.sum_extendedOldCoefficient, `JetsAuthorExpected.expected_sum_extendedOldCoefficient), (`ZetaNine.CoefficientMapFormalTransportJets.sum_extendedRemainderCoefficient, `JetsAuthorExpected.expected_sum_extendedRemainderCoefficient), (`ZetaNine.CoefficientMapFormalTransportJets.sum_previousRemainderCoefficient, `JetsAuthorExpected.expected_sum_previousRemainderCoefficient), (`ZetaNine.CoefficientMapFormalTransportJets.actual_chosen_all_rho_transport, `JetsAuthorExpected.expected_actual_chosen_all_rho_transport)] do
    let .thmInfo a ← getConstInfo actual | throwError "Actual source declaration is not a theorem: {actual}"
    let .thmInfo b ← getConstInfo expected | throwError "Expected closed declaration is not a theorem: {expected}"
    let same ← isDefEq a.type b.type
    unless same do throwError "Actual complete type differs from the original frozen header: {actual}"
    let aa ← Lean.collectAxioms actual
    let ba ← Lean.collectAxioms expected
    let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
    unless aa.toList.all allowed.contains && ba.toList.all allowed.contains do
      throwError "Nonstandard source/expected axioms: {actual}"
    IO.println (Json.mkObj [("kind",Json.str "actual_complete_source_expected_type"),
      ("declaration",Json.str actual.toString),("expected",Json.str expected.toString),
      ("full_source_type_expression_repr",Json.str (reprStr a.type)),
      ("full_expected_type_expression_repr",Json.str (reprStr b.type)),
      ("full_source_proof_expression_repr",Json.str (reprStr a.value)),
      ("type_kernel_equal",toJson same),
      ("source_axioms",toJson (aa.toList.map Name.toString)),
      ("expected_axioms",toJson (ba.toList.map Name.toString))]).compress
