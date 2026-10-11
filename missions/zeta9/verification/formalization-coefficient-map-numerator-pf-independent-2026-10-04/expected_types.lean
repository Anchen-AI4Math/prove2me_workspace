import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
import Lean
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
open ZetaNine.CoefficientMapFormalTransportData
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapPartialFractions
open ZetaNine.CoefficientMapNumeratorPartialFractions
namespace NumeratorPFIndependentExpected

theorem connectionPair_spec : ∀ (n : ℕ), 1 ≤ n → ∀ (r : Fin 5),
    (connectionP n r).natDegree ≤ 4 ∧ (connectionQ n r).natDegree ≤ 9 ∧
      ZetaNine.CoefficientMapConnection.connectionD n *
        (connectionP n r).comp (ZetaNine.CoefficientMapConnection.connectionU n) +
      ZetaNine.CoefficientMapConnection.connectionH n (connectionQ n r) =
        (ZetaNine.CoefficientMapConnection.connectionTarget n r.val).comp
          (ZetaNine.CoefficientMapConnection.connectionU n) :=
  ZetaNine.CoefficientMapFormalTransportData.connectionPair_spec

theorem numeratorClearedSeries_denominator_identity : ∀ (m j : ℕ) (A : ℚ[X]),
    numeratorClearedSeries m j A *
      (ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
        (A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_denominator_identity

theorem numeratorClearedSeries_unique : ∀ (m j : ℕ) (A : ℚ[X]) (S : PowerSeries ℚ),
    S * (ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
      (A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) →
    S = numeratorClearedSeries m j A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorClearedSeries_unique

theorem numeratorLocalTruncation_comp_eq_sum : ∀ (m j : ℕ) (A : ℚ[X]),
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ)) =
      ∑ s ∈ Icc 1 9, C (numeratorLocalCoefficient m j s A) *
        (X + C (j : ℚ)) ^ (9 - s) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_comp_eq_sum

theorem numeratorPartialNumerator_eq_sum_blocks : ∀ (m : ℕ) (A : ℚ[X]),
    numeratorPartialNumerator m A = ∑ j ∈ range (m + 1), numeratorPartialBlock m j A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_eq_sum_blocks

theorem numeratorPartialBlock_comp_own_shift : ∀ (m j : ℕ) (A : ℚ[X]),
    (numeratorPartialBlock m j A).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) =
      ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j ^ 9 *
        numeratorLocalTruncation m j A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_comp_own_shift

theorem numerator_own_block_matches_nine_jets : ∀ (m j : ℕ) (A : ℚ[X]),
    (X : ℚ[X]) ^ 9 ∣ A.comp (ZetaNine.CoefficientMapJet.shiftedVariable j) -
      (numeratorPartialBlock m j A).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_own_block_matches_nine_jets

theorem numerator_different_block_pole_divisibility : ∀ (m i j : ℕ) (A : ℚ[X]),
    j ≤ m → j ≠ i → (X + C (j : ℚ)) ^ 9 ∣ numeratorPartialBlock m i A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_pole_divisibility

theorem numerator_different_block_shift_X_pow_dvd : ∀ (m i j : ℕ) (A : ℚ[X]),
    j ≤ m → j ≠ i → (X : ℚ[X]) ^ 9 ∣
      (numeratorPartialBlock m i A).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_different_block_shift_X_pow_dvd

theorem numerator_full_candidate_matches_nine_jets : ∀ (m j : ℕ) (A : ℚ[X]),
    j ≤ m → (X : ℚ[X]) ^ 9 ∣
      (A - numeratorPartialNumerator m A).comp (ZetaNine.CoefficientMapJet.shiftedVariable j) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_full_candidate_matches_nine_jets

theorem numerator_denominator_divides_actual_candidate_difference : ∀ (m : ℕ) (A : ℚ[X]),
    polePolynomial m ^ 9 ∣ A - numeratorPartialNumerator m A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_denominator_divides_actual_candidate_difference

theorem numeratorCandidateClearedSeries_denominator_identity : ∀ (m j : ℕ) (A : ℚ[X]),
    numeratorCandidateClearedSeries m j A *
      (ZetaNine.CoefficientMapJet.shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9 =
        ((numeratorPartialNumerator m A).comp
          (ZetaNine.CoefficientMapJet.shiftedVariable j) : PowerSeries ℚ) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries_denominator_identity

theorem numerator_candidate_first_nine_coefficients : ∀ (m j : ℕ) (A : ℚ[X]),
    j ≤ m → ∀ (k : ℕ), k < 9 →
    PowerSeries.coeff k (numeratorCandidateClearedSeries m j A) =
      PowerSeries.coeff k (numeratorClearedSeries m j A) :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_candidate_first_nine_coefficients

theorem numerator_candidate_local_coefficients : ∀ (m j s : ℕ) (A : ℚ[X]),
    j ≤ m → 1 ≤ s → s ≤ 9 →
    PowerSeries.coeff (9 - s) (numeratorCandidateClearedSeries m j A) =
      numeratorLocalCoefficient m j s A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_candidate_local_coefficients

theorem numeratorLocalTruncation_natDegree_le : ∀ (m j : ℕ) (A : ℚ[X]),
    (numeratorLocalTruncation m j A).natDegree ≤ 8 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation_natDegree_le

theorem numeratorPartialBlock_natDegree_le : ∀ (m j : ℕ) (A : ℚ[X]),
    j ≤ m → (numeratorPartialBlock m j A).natDegree ≤ 9 * m + 8 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock_natDegree_le

theorem numeratorPartialNumerator_natDegree_le : ∀ (m : ℕ) (A : ℚ[X]),
    (numeratorPartialNumerator m A).natDegree ≤ 9 * m + 8 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator_natDegree_le

theorem actual_numerator_polynomial_partial_fractions : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → A = numeratorPartialNumerator m A :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_polynomial_partial_fractions

theorem numerator_partial_term_division : ∀ (m j s : ℕ) (A : ℚ[X]) (t : ℚ),
    j ≤ m → 1 ≤ s → s ≤ 9 → (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
    (numeratorLocalCoefficient m j s A * (clearedPolePolynomial m j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial m).eval t ^ 9 =
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_partial_term_division

theorem actual_numerator_global_partial_fractions : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) → ∀ (t : ℚ), (∀ k ≤ m, t + (k : ℚ) ≠ 0) →
    A.eval t / (polePolynomial m).eval t ^ 9 =
      ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
        numeratorLocalCoefficient m j s A / (t + (j : ℚ)) ^ s :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_global_partial_fractions

theorem numerator_local_coefficient_weighted_agreement : ∀ (m j s : ℕ) (W : ℚ[X]),
    numeratorLocalCoefficient m j s (weightedNumerator m W) =
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient m j s W :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numerator_local_coefficient_weighted_agreement

theorem numeratorLocalCoefficient_sub : ∀ (m j s : ℕ) (A B : ℚ[X]),
    numeratorLocalCoefficient m j s (A - B) =
      numeratorLocalCoefficient m j s A - numeratorLocalCoefficient m j s B :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalCoefficient_sub

theorem actual_numerator_all_local_coefficients_zero_implies_zero : ∀ (m : ℕ) (A : ℚ[X]),
    A.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 → numeratorLocalCoefficient m j s A = 0) → A = 0 :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_all_local_coefficients_zero_implies_zero

theorem actual_numerator_local_coefficients_injective : ∀ (m : ℕ) (A B : ℚ[X]),
    A.natDegree < 9 * (m + 1) → B.natDegree < 9 * (m + 1) →
    (∀ j ≤ m, ∀ s, 1 ≤ s → s ≤ 9 →
      numeratorLocalCoefficient m j s A = numeratorLocalCoefficient m j s B) → A = B :=
  ZetaNine.CoefficientMapNumeratorPartialFractions.actual_numerator_local_coefficients_injective

end NumeratorPFIndependentExpected
