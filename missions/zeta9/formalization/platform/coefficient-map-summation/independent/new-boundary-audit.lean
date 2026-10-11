import Solutions.Sol_ZetaNine_CoefficientMapSummation_actualSeries_hasSum_exactL
import Lean
open Lean Meta Polynomial
open ZetaNine.CoefficientMapReflection ZetaNine.CoefficientMapSummation
set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes false

theorem sum_review_absolute_strong_has_no_even_premise (n : ℕ) (W : ℚ[X])
    (hs : StrongProperMultiplier n W) : Summable (fun k : ℕ => ‖actualSeries n W k‖) :=
  actualSeries_norm_summable n W hs

theorem sum_review_actual_odd_constant_is_absolute :
    Summable (fun k : ℕ => ‖actualSeries 1 (1 : ℚ[X]) k‖) := by
  exact actualSeries_norm_summable 1 1 (by norm_num [StrongProperMultiplier])

theorem sum_review_public_HasSum_supplies_summability (n : ℕ) (hn : Even n)
    (W : ℚ[X]) (hs : StrongProperMultiplier n W) : Summable (actualSeries n W) :=
  (solution n hn W hs).summable

theorem sum_review_public_HasSum_supplies_exact_tsum (n : ℕ) (hn : Even n)
    (W : ℚ[X]) (hs : StrongProperMultiplier n W) :
    (∑' k : ℕ, actualSeries n W k) = exactL n W :=
  (solution n hn W hs).tsum_eq

theorem sum_review_original_boundary_even_two_X_four :
    HasSum (actualSeries 2 (((X : ℤ[X]) ^ 4).map (Int.castRingHom ℚ)))
      (exactL 2 (((X : ℤ[X]) ^ 4).map (Int.castRingHom ℚ))) := by
  exact original_integer_quartic_exact_infinite_L 2 (by norm_num) (by decide)
    ((X : ℤ[X]) ^ 4) (by norm_num [Polynomial.natDegree_pow])

theorem sum_review_actual_zero_X_three_term_at_two :
    actualSeries 0 ((X : ℚ[X]) ^ 3) 1 = 1 / 8 := by
  norm_num [actualSeries, ZetaNine.CoefficientMap.weightedR,
    ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.numerator,
    ZetaNine.CoefficientMap.poleProduct]

theorem sum_review_actual_zero_X_four_term_at_two :
    actualSeries 0 ((X : ℚ[X]) ^ 4) 1 = 1 / 2 := by
  norm_num [actualSeries, ZetaNine.CoefficientMap.weightedR,
    ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.numerator,
    ZetaNine.CoefficientMap.poleProduct]

theorem sum_review_actual_series_starts_at_positive_one (n : ℕ) (W : ℚ[X]) :
    actualSeries n W 0 = (ZetaNine.CoefficientMap.weightedR n W 1 : ℝ) := rfl

run_meta do
  for name in [
    `sum_review_absolute_strong_has_no_even_premise,
    `sum_review_actual_odd_constant_is_absolute,
    `sum_review_public_HasSum_supplies_summability,
    `sum_review_public_HasSum_supplies_exact_tsum,
    `sum_review_original_boundary_even_two_X_four,
    `sum_review_actual_zero_X_three_term_at_two,
    `sum_review_actual_zero_X_four_term_at_two,
    `sum_review_actual_series_starts_at_positive_one] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString))]).compress
