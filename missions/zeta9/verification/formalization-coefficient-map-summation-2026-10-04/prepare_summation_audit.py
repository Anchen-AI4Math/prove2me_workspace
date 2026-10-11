from pathlib import Path
import re

out = Path(__file__).resolve().parent
task = out.parents[1]
source = task / 'formalization/CoefficientMapSummation.lean'
names = re.findall(r'^(?:def|theorem) (\w+)', source.read_text(encoding='utf-8-sig'), re.M)
assert len(names) == 24
checks = ['checked_original_Eq_four_tsum', 'checked_absolute_and_HasSum',
    'checked_unconditional_finite_odd', 'checked_tail_including_simple_poles',
    'checked_n_zero_X_four_boundary', 'checked_n_zero_X_four_actual_series',
    'checked_n_zero_constant_HasSum']
text = '''import missions.zeta9.formalization.CoefficientMapSummation
import Lean

open Lean Meta Polynomial Filter
open scoped BigOperators Topology
open ZetaNine.CoefficientMapInjectivity ZetaNine.CoefficientMapReflection
open ZetaNine.CoefficientMapSummation
set_option pp.fullNames true
set_option pp.universes false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

-- The actual positive-integer series, with the original integer quartic domain.
theorem checked_original_Eq_four_tsum (n : ℕ) (hn2 : 2 ≤ n) (hn : Even n)
    (W : ℤ[X]) (hW : W.natDegree ≤ 4) :
    (∑' t : ℕ, (ZetaNine.CoefficientMap.weightedR n (W.map (Int.castRingHom ℚ))
      ((t + 1 : ℕ) : ℚ) : ℝ)) =
      (ZetaNine.CoefficientMapFiniteSum.constantTerm n (W.map (Int.castRingHom ℚ)) : ℝ) +
        ((ZetaNine.CoefficientMapFiniteSum.rho n 3 (W.map (Int.castRingHom ℚ)) : ℝ) * (riemannZeta (3 : ℂ)).re +
         (ZetaNine.CoefficientMapFiniteSum.rho n 5 (W.map (Int.castRingHom ℚ)) : ℝ) * (riemannZeta (5 : ℂ)).re +
         (ZetaNine.CoefficientMapFiniteSum.rho n 7 (W.map (Int.castRingHom ℚ)) : ℝ) * (riemannZeta (7 : ℂ)).re +
         (ZetaNine.CoefficientMapFiniteSum.rho n 9 (W.map (Int.castRingHom ℚ)) : ℝ) * (riemannZeta (9 : ℂ)).re) := by
  simpa only [actualSeries, exactL, zetaReal, Nat.cast_ofNat] using
    (original_integer_quartic_exact_infinite_L n hn2 hn W hW).tsum_eq

theorem checked_absolute_and_HasSum (n : ℕ) (hn : Even n) (W : ℚ[X])
    (h : 2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2) :
    Summable (fun t : ℕ => ‖(ZetaNine.CoefficientMap.weightedR n W
      ((t + 1 : ℕ) : ℚ) : ℝ)‖) ∧
    HasSum (fun t : ℕ => (ZetaNine.CoefficientMap.weightedR n W ((t + 1 : ℕ) : ℚ) : ℝ))
      (exactL n W) :=
  ⟨actualSeries_norm_summable n W h, actualSeries_hasSum_exactL n hn W h⟩

theorem checked_unconditional_finite_odd (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (h : 2 * n + 2 * W.natDegree ≤ 9 * (n + 1) - 2) :
    ZetaNine.CoefficientMapFiniteSum.finiteL n T W =
      ZetaNine.CoefficientMapFiniteSum.constantTerm n W +
        (ZetaNine.CoefficientMapFiniteSum.rho n 3 W * ZetaNine.HarmonicStability.harmonicPower 3 T +
         ZetaNine.CoefficientMapFiniteSum.rho n 5 W * ZetaNine.HarmonicStability.harmonicPower 5 T +
         ZetaNine.CoefficientMapFiniteSum.rho n 7 W * ZetaNine.HarmonicStability.harmonicPower 7 T +
         ZetaNine.CoefficientMapFiniteSum.rho n 9 W * ZetaNine.HarmonicStability.harmonicPower 9 T) +
      ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W :=
  actual_finite_odd_identity n T hn W h

theorem checked_tail_including_simple_poles (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (ZetaNine.CoefficientMapFiniteSum.shiftedTail n T W : ℝ)) atTop (𝓝 0) :=
  actual_shiftedTail_tendsto_zero n W

theorem checked_n_zero_X_four_boundary :
    ProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧ ¬ StrongProperMultiplier 0 (X ^ 4 : ℚ[X]) ∧
      ZetaNine.CoefficientMapReflection.rho 0 1 (X ^ 4 : ℚ[X]) = 1 := by
  constructor
  · norm_num [ProperMultiplier]
  constructor
  · norm_num [StrongProperMultiplier]
  · norm_num [ZetaNine.CoefficientMapReflection.rho, ZetaNine.CoefficientMapJet.weightedLocalCoefficient,
      ZetaNine.CoefficientMapJet.weightedClearedSeries, ZetaNine.CoefficientMapJet.clearedSeries,
      ZetaNine.CoefficientMapJet.shiftedNumerator, ZetaNine.CoefficientMapJet.shiftedClearedDenominator,
      ZetaNine.CoefficientMapJet.localU, ZetaNine.CoefficientMapJet.shiftedVariable,
      Polynomial.pow_comp, Polynomial.X_comp, Polynomial.coe_mul, Polynomial.coe_pow,
      Polynomial.coe_X, ← pow_two, ← pow_mul]

theorem checked_n_zero_X_four_actual_series (t : ℕ) :
    actualSeries 0 (X ^ 4 : ℚ[X]) t = 1 / ((t : ℝ) + 1) := by
  have ht : ((t + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have h : ZetaNine.CoefficientMap.weightedR 0 (X ^ 4 : ℚ[X]) ((t + 1 : ℕ) : ℚ) =
      1 / ((t + 1 : ℕ) : ℚ) := by
    norm_num [ZetaNine.CoefficientMap.weightedR, ZetaNine.CoefficientMap.actualR,
      ZetaNine.CoefficientMap.numerator, ZetaNine.CoefficientMap.poleProduct]
    field_simp
  unfold actualSeries
  rw [h]
  push_cast
  rfl

theorem checked_n_zero_constant_HasSum :
    HasSum (actualSeries 0 (1 : ℚ[X])) (exactL 0 (1 : ℚ[X])) :=
  actualSeries_hasSum_exactL 0 (by norm_num) 1 (by norm_num [StrongProperMultiplier])

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
'''
text += ',\n'.join('    `ZetaNine.CoefficientMapSummation.' + n for n in names)
text += ',\n' + ',\n'.join('    `' + n for n in checks) + '] do emit name\n'
(out / 'type-audit.lean').write_text(text, encoding='utf-8')
