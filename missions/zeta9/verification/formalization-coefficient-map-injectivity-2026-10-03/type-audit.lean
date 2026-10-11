import missions.zeta9.formalization.CoefficientMapInjectivity
import Lean

open Lean Meta Polynomial
open ZetaNine.CoefficientMapInjectivity
set_option pp.fullNames true
set_option pp.universes false
set_option linter.unusedVariables false

-- Exact full-array statement, with both actual proper-degree hypotheses.
theorem checked_complete_local_array (n : ℕ) (W V : ℚ[X])
    (hW : 2 * n + 2 * W.natDegree < 9 * (n + 1))
    (hV : 2 * n + 2 * V.natDegree < 9 * (n + 1))
    (heq : ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
      ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s W =
        ZetaNine.CoefficientMapJet.weightedLocalCoefficient n j s V) : W = V :=
  local_coefficients_injective n W V hW hV heq

theorem checked_quartic_local_array (n : ℕ) (W V : ℚ[X])
    (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : fullLocalCoefficientMap n W = fullLocalCoefficientMap n V) : W = V := by
  have h := fullLocalCoefficientMap_injective n
    (a₁ := ⟨W, quartic_is_proper n W hW⟩)
    (a₂ := ⟨V, quartic_is_proper n V hV⟩) heq
  exact congrArg Subtype.val h

-- Original even n>=2 integer-quartic regime, with actual integer multipliers.
theorem checked_original_integer_quartic (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W V : ℤ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : fullLocalCoefficientMap n (W.map (Int.castRingHom ℚ)) =
      fullLocalCoefficientMap n (V.map (Int.castRingHom ℚ))) : W = V := by
  have hm := checked_quartic_local_array n (W.map (Int.castRingHom ℚ))
    (V.map (Int.castRingHom ℚ))
    (le_trans Polynomial.natDegree_map_le hW)
    (le_trans Polynomial.natDegree_map_le hV) heq
  exact Polynomial.map_injective (Int.castRingHom ℚ)
    (by intro a b hab; exact Int.cast_injective hab) hm

theorem checked_n_zero (W V : ℚ[X]) (hW : W.natDegree ≤ 4) (hV : V.natDegree ≤ 4)
    (heq : fullLocalCoefficientMap 0 W = fullLocalCoefficientMap 0 V) : W = V :=
  checked_quartic_local_array 0 W V hW hV heq

theorem checked_actual_weighted_rational_representation (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    (weightedNumerator n W).eval t / ((polePolynomial n).eval t) ^ 9 =
      ZetaNine.CoefficientMap.weightedR n W t := by
  simp only [weightedNumerator, Polynomial.eval_mul, Polynomial.eval_comp,
    baseNumerator_eval, baseU, Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C,
    polePolynomial, Polynomial.eval_prod, ZetaNine.CoefficientMap.weightedR,
    ZetaNine.CoefficientMap.actualR, ZetaNine.CoefficientMap.poleProduct]
  ring

run_meta do
  let emit (name : Name) : MetaM Unit := do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
  for name in [
    `ZetaNine.CoefficientMapInjectivity.baseNumerator,
    `ZetaNine.CoefficientMapInjectivity.baseU,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial,
    `ZetaNine.CoefficientMapInjectivity.AllLocalCoefficientsZero,
    `ZetaNine.CoefficientMapInjectivity.ProperMultiplier,
    `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_eval,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_shift,
    `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_shifted_numerator_divisibility,
    `ZetaNine.CoefficientMapInjectivity.zero_local_jet_implies_pole_divisibility,
    `ZetaNine.CoefficientMapInjectivity.pole_factors_coprime,
    `ZetaNine.CoefficientMapInjectivity.all_zero_jets_imply_full_denominator_divisibility,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_natDegree,
    `ZetaNine.CoefficientMapInjectivity.polePolynomial_pow_natDegree,
    `ZetaNine.CoefficientMapInjectivity.baseU_natDegree,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_ne_zero,
    `ZetaNine.CoefficientMapInjectivity.baseNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_natDegree_le,
    `ZetaNine.CoefficientMapInjectivity.weightedNumerator_zero_implies_multiplier_zero,
    `ZetaNine.CoefficientMapInjectivity.all_local_coefficients_zero_implies_zero,
    `ZetaNine.CoefficientMapInjectivity.weightedLocalCoefficient_sub,
    `ZetaNine.CoefficientMapInjectivity.local_coefficients_injective,
    `ZetaNine.CoefficientMapInjectivity.fullLocalCoefficientMap_injective,
    `ZetaNine.CoefficientMapInjectivity.quartic_is_proper,
    `checked_complete_local_array, `checked_quartic_local_array,
    `checked_original_integer_quartic, `checked_n_zero,
    `checked_actual_weighted_rational_representation] do emit name
