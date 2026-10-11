import missions.zeta9.formalization.CoefficientMapFiniteSum
import Lean

open Lean Meta Polynomial
open scoped BigOperators
open ZetaNine.CoefficientMapFiniteSum ZetaNine.HarmonicStability
set_option pp.fullNames true
set_option pp.universes false

theorem checked_finite_T_zero (n : ℕ) (W : ℚ[X]) : finiteL n 0 W = 0 := by
  simp [finiteL]

theorem checked_constant_n_zero (W : ℚ[X]) : constantTerm 0 W = 0 := by
  simp [constantTerm, harmonicPower]

theorem checked_tail_n_zero (T : ℕ) (W : ℚ[X]) : shiftedTail 0 T W = 0 := by
  simp [shiftedTail]

theorem checked_simple_pole_retained : rho 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  norm_num [rho, ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
    ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
    ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
    ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
    Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_n_zero_X_four_actual_finite (T : ℕ) :
    finiteL 0 T (X ^ 4 : ℚ[X]) = harmonicPower 1 T := by
  unfold finiteL harmonicPower
  apply Finset.sum_congr rfl
  intro t ht
  have htpos : (0 : ℚ) < (t : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp ht).1
  have htne := ne_of_gt htpos
  norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
    ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
  field_simp

theorem checked_odd_identity_exact (n T : ℕ) (W : ℚ[X])
    (hproper : ZetaNine.CoefficientMapInjectivity.ProperMultiplier n W)
    (h1 : rho n 1 W = 0) (h2 : rho n 2 W = 0) (h4 : rho n 4 W = 0)
    (h6 : rho n 6 W = 0) (h8 : rho n 8 W = 0) :
    finiteL n T W = constantTerm n W +
      (rho n 3 W * harmonicPower 3 T + rho n 5 W * harmonicPower 5 T +
       rho n 7 W * harmonicPower 7 T + rho n 9 W * harmonicPower 9 T) + shiftedTail n T W :=
  actual_grouped_finite_identity_odd n T W hproper h1 h2 h4 h6 h8

run_meta do
  for name in [
    `ZetaNine.CoefficientMapFiniteSum.rho,
    `ZetaNine.CoefficientMapFiniteSum.constantTerm,
    `ZetaNine.CoefficientMapFiniteSum.finiteL,
    `ZetaNine.CoefficientMapFiniteSum.shiftedTail,
    `ZetaNine.CoefficientMapFiniteSum.harmonicPower_succ,
    `ZetaNine.CoefficientMapFiniteSum.shifted_harmonic_sum,
    `ZetaNine.CoefficientMapFiniteSum.actual_finite_harmonic_identity,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_no_simple_pole,
    `ZetaNine.CoefficientMapFiniteSum.actual_grouped_finite_identity_odd,
    `ZetaNine.CoefficientMapFiniteSum.harmonic_difference_eq_shifted,
    `checked_finite_T_zero, `checked_constant_n_zero, `checked_tail_n_zero,
    `checked_simple_pole_retained, `checked_n_zero_X_four_actual_finite,
    `checked_odd_identity_exact] do
    let ci ← getConstInfo name
    let typ ← ppExpr ci.type
    let axs ← Lean.collectAxioms name
    let value ← match ci with
      | .defnInfo d => pure (Json.str (← ppExpr d.value).pretty)
      | _ => pure Json.null
    IO.println (Json.mkObj [("declaration", Json.str name.toString),
      ("type", Json.str typ.pretty), ("axioms", toJson (axs.toList.map Name.toString)),
      ("definitionValue", value)]).compress
