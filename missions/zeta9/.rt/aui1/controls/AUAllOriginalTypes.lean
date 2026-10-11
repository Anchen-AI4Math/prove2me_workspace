import AUExprDag
import AnalyticWeightedBound
import Lean
import Lean.Util.CollectAxioms
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 200000
noncomputable section
open scoped BigOperators Topology
open Set Finset Filter Polynomial
open ZetaNine
open Lean Meta Elab Command
open ZetaNine.AnalyticFactorialBounds
open ZetaNine.AnalyticMomentBounds
open ZetaNine.AnalyticPSeriesTail
open ZetaNine.AnalyticPhase
open ZetaNine.AnalyticRationalFactorial
open ZetaNine.AnalyticRationalLogBound
open ZetaNine.AnalyticRationalTail
open ZetaNine.AnalyticUniformMomentBound
open ZetaNine.AnalyticWeightedBound
open ZetaNine.CoefficientMap

private def afEmit (j : Json) : MetaM Unit := do
  let action : IO Unit := do
    let stdout ← IO.getStdout
    stdout.putStrLn ("AU_RECORD|" ++ j.compress)
    stdout.flush
  liftM action

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let some value := ci.value? true | throwError "Missing complete proof/definition value: {n}"
  let payload ← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip ci.type value)
  let (rt,rv) ← ofExcept (IndependentLosslessExprDagV1.decode payload)
  let exactType := Expr.equal ci.type rt
  let exactValue := Expr.equal value rv
  unless exactType && exactValue do throwError "Full-field Expr DAG changed an expression: {n}"
  let typeKernel ← isDefEq ci.type rt
  let valueKernel ← isDefEq value rv
  let typed ← isDefEq (← inferType rv) ci.type
  unless typeKernel && valueKernel && typed do
    throwError "Complete reconstructed proof/value does not have its exact complete type: {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",toJson payload.compress),
    ("value_raw_format",toJson "lossless lean-expr-dag-v1; full type_root and value_root"),
    ("all_fields_type_Expr_equal",toJson exactType),("all_fields_value_Expr_equal",toJson exactValue),
    ("full_type_kernel_equal",toJson typeKernel),("full_value_kernel_equal",toJson valueKernel),
    ("value_type_isDefEq",toJson typed),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]

namespace AUAllOriginal

theorem complete_000 (n j : ℕ) (hj : j ≤ n) (t : ℚ) :
    ZetaNine.CoefficientMap.poleProduct n t = (t + j) * ZetaNine.CoefficientMap.clearedPoleProduct n j t := ZetaNine.CoefficientMap.poleProduct_factor

theorem complete_001 (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : ZetaNine.CoefficientMap.poleProduct n t ≠ 0 := ZetaNine.CoefficientMap.poleProduct_ne_zero

theorem complete_002 (n j : ℕ) :
    ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero

theorem complete_003 (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.actualR n t * (t + j) ^ 9 = ZetaNine.CoefficientMap.clearedR n j t := ZetaNine.CoefficientMap.clear_highest_pole

theorem complete_004 (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (t : ℚ) (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n W t * (t + j) ^ 9 = ZetaNine.CoefficientMap.clearedWeightedR n j W t := ZetaNine.CoefficientMap.clear_weighted_highest_pole

theorem complete_005 (a n : ℕ) :
    (∏ i ∈ range n, ((a : ℚ) + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((a + n).choose n : ℚ) := ZetaNine.CoefficientMap.rising_product

theorem complete_006 (n : ℕ) :
    (∏ k ∈ range n, ((k : ℚ) - n)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) := ZetaNine.CoefficientMap.falling_product

theorem complete_007 (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) =
      (-1 : ℚ) ^ j * (j.factorial : ℚ) * ((n - j).factorial : ℚ) := ZetaNine.CoefficientMap.clearedPoleProduct_eval

theorem complete_008 (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.numerator n (-(j : ℚ)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := ZetaNine.CoefficientMap.numerator_eval

theorem complete_009 (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := ZetaNine.CoefficientMap.leadingPoleCoefficient_eq

theorem complete_010 (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even

theorem complete_011 (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j ≠ 0 := ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero

theorem complete_012 (n j : ℕ) (hj : j ≤ n) :
    ∃ z : ℤ, ZetaNine.CoefficientMap.leadingPoleCoefficient n j = (z : ℚ) := ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer

theorem complete_013 (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    (-1 : ℚ) ^ j * ZetaNine.CoefficientMap.leadingPoleCoefficient n j > 0 := ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even

theorem complete_014 (n j : ℕ) (hj : j ≤ n) (z : ℚ) :
    (-(j : ℚ) + z) * (-(j : ℚ) + z + n) =
      -(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2 := ZetaNine.CoefficientMap.local_coordinate_identity

theorem complete_015 (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (z : ℚ) :
    ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ) + z) =
      ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ) + z) *
        W.eval (-(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2) := ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate

theorem complete_016 (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq

theorem complete_017 (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even

theorem complete_018 (n : ℕ) : 0 < (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.real_factorial_pos

theorem complete_019 (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_succ

theorem complete_020 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper

theorem complete_021 (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower

theorem complete_022 (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_lower

theorem complete_023 (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := ZetaNine.AnalyticFactorialBounds.log_factorial_upper

theorem complete_024 (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_pred

theorem complete_025 (n : ℕ) : (n.factorial : ℚ) ≠ 0 := ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero

theorem complete_026 (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.ascending_product_factorial

theorem complete_027 (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial

theorem complete_028 (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial

theorem complete_029 (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial

theorem complete_030 (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := ZetaNine.AnalyticRationalFactorial.actualR_factorial

theorem complete_031 (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := ZetaNine.AnalyticRationalFactorial.actualR_factorial_real

theorem complete_032 (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := ZetaNine.AnalyticRationalFactorial.actualR_pos

theorem complete_033 (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := ZetaNine.AnalyticRationalFactorial.actualR_real_pos

theorem complete_034 (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := ZetaNine.AnalyticRationalFactorial.actualR_log_factorial

theorem complete_035 (x : ℝ) :
    (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 =
    (743876235460997060507 / 100000000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 0 +
    (109589356802878649457 / 100000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 1 +
    (10634683646357555663 / 2000000000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 2 +
    (29280046551142071 / 2500000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 3 +
    (1524457114482447 / 100000000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 4 +
    (32277046531191 / 2500000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 5 +
    (73792828347 / 10000000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 6 +
    (71169471 / 25000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 7 +
    (1428963 / 2000 : ℝ) * (x - (101 / 100 : ℝ)) ^ 8 +
    (1057 / 10 : ℝ) * (x - (101 / 100 : ℝ)) ^ 9 +
    (7 / 1 : ℝ) * (x - (101 / 100 : ℝ)) ^ 10 := ZetaNine.AnalyticPhase.phaseGap_identity

theorem complete_036 (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    0 < (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 := ZetaNine.AnalyticPhase.phaseGap_pos

theorem complete_037 (x : ℝ) (hx : 1 < x) : 0 < ZetaNine.AnalyticPhase.phaseRatio x := ZetaNine.AnalyticPhase.phaseRatio_pos

theorem complete_038 (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phaseRatio x < 1 := ZetaNine.AnalyticPhase.phaseRatio_lt_one

theorem complete_039 (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phaseSlope x = Real.log (ZetaNine.AnalyticPhase.phaseRatio x) := ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio

theorem complete_040 (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phaseSlope x < 0 := ZetaNine.AnalyticPhase.phaseSlope_neg_right

theorem complete_041 (x a : ℝ) (ha : x + a ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a))
      (Real.log (x + a) + 1) x := ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift

theorem complete_042 (x : ℝ) (hx : 1 < x) :
    HasDerivAt ZetaNine.AnalyticPhase.phase (ZetaNine.AnalyticPhase.phaseSlope x) x := ZetaNine.AnalyticPhase.phase_hasDerivAt

theorem complete_043 (x : ℝ) (hx : 1 < x) : deriv ZetaNine.AnalyticPhase.phase x = ZetaNine.AnalyticPhase.phaseSlope x := ZetaNine.AnalyticPhase.deriv_phase

theorem complete_044 : StrictAntiOn ZetaNine.AnalyticPhase.phase (Ici (101 / 100 : ℝ)) := ZetaNine.AnalyticPhase.phase_strictAntiOn_right

theorem complete_045 (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phase x ≤ ZetaNine.AnalyticPhase.phase (101 / 100) := ZetaNine.AnalyticPhase.phase_le_right_endpoint

theorem complete_046 : 0 < ZetaNine.AnalyticPhase.upperSlopeConstant := ZetaNine.AnalyticPhase.upperSlopeConstant_pos

theorem complete_047 : ZetaNine.AnalyticPhase.upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := ZetaNine.AnalyticPhase.upperSlopeConstant_eq

theorem complete_048 (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : ZetaNine.AnalyticPhase.phaseRatio (1 + u) ≤ ZetaNine.AnalyticPhase.upperSlopeConstant / u := ZetaNine.AnalyticPhase.phaseRatio_small_interval_le

theorem complete_049 (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : ZetaNine.AnalyticPhase.phaseSlope (1 + u) ≤ Real.log (ZetaNine.AnalyticPhase.upperSlopeConstant / u) := ZetaNine.AnalyticPhase.phaseSlope_small_interval_le

theorem complete_050 : ZetaNine.AnalyticPhase.phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := ZetaNine.AnalyticPhase.phase_one_eq

theorem complete_051 : ZetaNine.AnalyticPhase.smoothPhaseGap 1 = 0 := ZetaNine.AnalyticPhase.smoothPhaseGap_one

theorem complete_052 (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt ZetaNine.AnalyticPhase.smoothPhaseGap (ZetaNine.AnalyticPhase.smoothPhaseSlope x) x := ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt

theorem complete_053 (x : ℝ) (hx : 1 ≤ x) :
    0 < ZetaNine.AnalyticPhase.smoothPhaseRatio x := ZetaNine.AnalyticPhase.smoothPhaseRatio_pos

theorem complete_054 (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseRatio x ≤ ZetaNine.AnalyticPhase.upperSlopeConstant := ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant

theorem complete_055 (x : ℝ) (hx : 1 ≤ x) :
    ZetaNine.AnalyticPhase.smoothPhaseSlope x =
      Real.log (ZetaNine.AnalyticPhase.smoothPhaseRatio x) - Real.log ZetaNine.AnalyticPhase.upperSlopeConstant := ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio

theorem complete_056 (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseSlope x ≤ 0 := ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos

theorem complete_057 :
    AntitoneOn ZetaNine.AnalyticPhase.smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ)) := ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn

theorem complete_058 (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseGap x ≤ 0 := ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero

theorem complete_059 (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    u * (1 + Real.log (a / u)) ≤ a := ZetaNine.AnalyticPhase.mul_one_add_log_div_le

theorem complete_060 (u : ℝ) (hu : 0 < u) :
    ZetaNine.AnalyticPhase.phase (1 + u) = ZetaNine.AnalyticPhase.phase 1 +
      u * (1 + Real.log (ZetaNine.AnalyticPhase.upperSlopeConstant / u)) + ZetaNine.AnalyticPhase.smoothPhaseGap (1 + u) := ZetaNine.AnalyticPhase.phase_small_interval_identity

theorem complete_061 (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.phase (1 + u) ≤ ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant := ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant

theorem complete_062 (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phase x ≤ ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant := ZetaNine.AnalyticPhase.phase_global_le_one_add_constant

theorem complete_063 : (693147 / 1000000 : ℝ) < Real.log 2 := ZetaNine.AnalyticPhase.log_two_lower_rational

theorem complete_064 : Real.log 3 < (1098613 / 1000000 : ℝ) := ZetaNine.AnalyticPhase.log_three_upper_rational

theorem complete_065 :
    ZetaNine.AnalyticPhase.upperSlopeConstant < (309 / 100000 : ℝ) := ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational

theorem complete_066 :
    ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant < (-10564011 / 1000000 : ℝ) := ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified

theorem complete_067 (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phase x < (-10564011 / 1000000 : ℝ) := ZetaNine.AnalyticPhase.phase_global_lt_certified

theorem complete_068 :
    ∀ x : ℝ, 1 < x → ZetaNine.AnalyticPhase.phase x ≤ (-2641 / 250 : ℝ) := ZetaNine.AnalyticPhase.phase_global_upper_bound

theorem complete_069 (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := ZetaNine.AnalyticRationalLogBound.scaled_phase_identity

theorem complete_070 (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase

theorem complete_071 (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified

theorem complete_072 (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticRationalLogBound.actualR_le_certified

theorem complete_073 (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticRationalLogBound.actualR_compact_bound

theorem complete_074 (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := ZetaNine.AnalyticRationalTail.actual_falling_product_le

theorem complete_075 (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le

theorem complete_076 (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := ZetaNine.AnalyticRationalTail.actual_poleProduct_ge

theorem complete_077 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational

theorem complete_078 (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := ZetaNine.AnalyticRationalTail.actualR_tail_bound

theorem complete_079 (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := ZetaNine.AnalyticRationalTail.actual_tail_weight_le

theorem complete_080 (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow

theorem complete_081 (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable

theorem complete_082 (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound

theorem complete_083 (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored

theorem complete_084 (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le

theorem complete_085 (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k = 0 := ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le

theorem complete_086 (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k := ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg

theorem complete_087 (n r m : ℕ) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg

theorem complete_088 (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := ZetaNine.AnalyticMomentBounds.actual_compact_weight_le

theorem complete_089 (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound

theorem complete_090 (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ ZetaNine.AnalyticMomentBounds.tailPower n r := ZetaNine.AnalyticMomentBounds.tailPower_ge

theorem complete_091 (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r := ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg

theorem complete_092 (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (k : ℝ) ^ ZetaNine.AnalyticMomentBounds.tailPower n r := ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound

theorem complete_093 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (ZetaNine.AnalyticMomentBounds.actualMomentSequence n r) := ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable

theorem complete_094 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m‖) := ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable

theorem complete_095 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound

theorem complete_096 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound

theorem complete_097 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r = (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) +
      ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n) := ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail

theorem complete_098 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound

theorem complete_099 (r : ℕ) : 0 < ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r := ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos

theorem complete_100 (r : ℕ) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r ≤ (729 / 224 : ℝ) := ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le

theorem complete_101 (n r : ℕ) (hn : 1 ≤ n) : 0 < ZetaNine.AnalyticUniformMomentBound.tailMajorant n r := ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos

theorem complete_102 (r : ℕ) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant

theorem complete_103 (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (ZetaNine.AnalyticMomentBounds.tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity

theorem complete_104 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) ≤ Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) + 7 -
      ZetaNine.AnalyticUniformMomentBound.tailExponent * n - 2 * Real.log (n : ℝ) := ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper

theorem complete_105 :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < ZetaNine.AnalyticUniformMomentBound.tailExponent := ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap

theorem complete_106 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound

theorem complete_107 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound

theorem complete_108 : 0 < ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos

theorem complete_109 (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤ ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound

theorem complete_110 (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum

theorem complete_111 (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r) := ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments

theorem complete_112 (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W) := ZetaNine.AnalyticWeightedBound.actualWeighted_summable

theorem complete_113 (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m‖) := ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable

theorem complete_114 (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r := ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum

theorem complete_115 (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.actualMoment n r := ZetaNine.AnalyticWeightedBound.actualMoment_nonneg

theorem complete_116 (n : ℕ) (W : ℚ[X]) :
    0 ≤ ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg

theorem complete_117 (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound

theorem complete_118 (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n (W n) m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n (W n) := ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound

theorem complete_119 : Tendsto ZetaNine.AnalyticWeightedBound.uniformError atTop (𝓝 0) := ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero

theorem complete_120 (n : ℕ) (hn : 1 ≤ n) :
    ZetaNine.AnalyticWeightedBound.analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + ZetaNine.AnalyticWeightedBound.uniformError n) * n) := ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent

theorem complete_121 :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one

end AUAllOriginal

private def afProofHelpers (actual expected : Name) (av bv : Expr) : MetaM (Expr × Expr) := do
  let mut aa := av
  let mut bb := bv
  for _ in [:16] do
    let mut amap : Array (Name × Expr) := #[]
    let mut bmap : Array (Name × Expr) := #[]
    for n in aa.getUsedConstants do
      if n.getPrefix.getPrefix == actual.getPrefix && n.getString!.startsWith "_proof_" then
        let a ← getConstInfo n
        let some va0 := a.value? true | throwError "Missing actual helper proof {n}"
        let mut matched : Option Name := none
        for m in bb.getUsedConstants do
          if m.getPrefix.getPrefix == expected.getPrefix && m.getString!.startsWith "_proof_" then
            let c ← getConstInfo m
            if let some vc := c.value? true then
              if Expr.equal a.type c.type && Expr.equal va0 vc then matched := some m
        let some paired := matched | throwError "No full-expression identical expected helper for {n}"
        let b ← getConstInfo paired
        unless (← isProp a.type) && (← isProp b.type) do
          throwError "Only proposition-valued compiler proof helpers can be expanded {n}"
        unless a.levelParams.isEmpty && b.levelParams.isEmpty do
          throwError "Unexpected helper universes {n}"
        let some va := a.value? true | throwError "Missing full helper proof value {n}"
        let some vb := b.value? true | throwError "Missing full helper proof value {paired}"
        let typeDefEq ← isDefEq a.type b.type
        let valueDefEq ← isDefEq va vb
        let actualValueTyped ← isDefEq (← inferType va) a.type
        let expectedValueTyped ← isDefEq (← inferType vb) b.type
        unless typeDefEq && valueDefEq && actualValueTyped && expectedValueTyped do
          throwError "Helper kernel mismatch {n} {paired}"
        afEmit <| Json.mkObj [("kind",toJson "definition_helper_compare"),
          ("actual",toJson n.toString),("expected",toJson paired.toString),
          ("type_actual_raw",toJson (reprStr a.type)),("type_expected_raw",toJson (reprStr b.type)),
          ("value_actual_raw",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip a.type va)),("value_expected_raw",← ofExcept (IndependentLosslessExprDagV1.persistedRoundTrip b.type vb)),
          ("type_exprEqual",toJson (Expr.equal a.type b.type)),("value_exprEqual",toJson (Expr.equal va vb)),
          ("type_isDefEq",toJson typeDefEq),("value_isDefEq",toJson valueDefEq),
          ("actual_value_typed",toJson actualValueTyped),("expected_value_typed",toJson expectedValueTyped),
          ("actual_axioms",← afAxioms n),("expected_axioms",← afAxioms paired)]
        amap := amap.push (n,va)
        bmap := bmap.push (paired,vb)
    if amap.isEmpty then return (aa,bb)
    aa := aa.replace fun e => match e with
      | .const n [] => (amap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
    bb := bb.replace fun e => match e with
      | .const n [] => (bmap.find? fun x => x.1 == n).map Prod.snd
      | _ => none
  throwError "Helper expansion did not terminate within the fixed bound"

private def afCompare (kind : String) (actual expected : Name) (requireValue : Bool) : MetaM Unit := do
  let a ← getConstInfo actual
  let b ← getConstInfo expected
  let typeEqual := Expr.equal a.type b.type
  let typeDefEq ← isDefEq a.type b.type
  unless typeDefEq do throwError "Type mismatch {actual} {expected}"
  let mut valueEqual := false
  let mut valueDefEq := false
  let mut normalizedEqual := false
  let mut normalizedDefEq := false
  let mut va := Json.null
  let mut vb := Json.null
  let mut normalizedA := Json.null
  let mut normalizedB := Json.null
  if requireValue then
    let some av := a.value? | throwError "No actual definition value {actual}"
    let some bv := b.value? | throwError "No original definition value {expected}"
    valueEqual := Expr.equal av bv
    valueDefEq ← isDefEq av bv
    va := toJson (reprStr av)
    vb := toJson (reprStr bv)
    let (na,nb) ← afProofHelpers actual expected av bv
    normalizedEqual := Expr.equal na nb
    normalizedDefEq ← isDefEq na nb
    normalizedA := toJson (reprStr na)
    normalizedB := toJson (reprStr nb)
  afEmit <| Json.mkObj [("kind",toJson kind),("actual",toJson actual.toString),
    ("expected",toJson expected.toString),("type_actual_raw",toJson (reprStr a.type)),
    ("type_expected_raw",toJson (reprStr b.type)),("type_exprEqual",toJson typeEqual),
    ("type_isDefEq",toJson typeDefEq),("value_actual_raw",va),("value_expected_raw",vb),
    ("value_exprEqual",toJson valueEqual),("value_isDefEq",toJson valueDefEq),
    ("normalized_value_actual_raw",normalizedA),("normalized_value_expected_raw",normalizedB),
    ("normalized_value_exprEqual",toJson normalizedEqual),("normalized_value_isDefEq",toJson normalizedDefEq),
    ("normalization",toJson "Only unfold all paired proposition-valued own compiler _proof_ helpers; no binder or metadata erasure"),
    ("actual_axioms",← afAxioms actual),("expected_axioms",← afAxioms expected)]
  if requireValue then
    unless valueDefEq && normalizedDefEq do throwError "Full definition kernel mismatch {actual}"

run_cmd liftTermElabM do
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.poleProduct_factor ``AUAllOriginal.complete_000 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_000
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.poleProduct_ne_zero ``AUAllOriginal.complete_001 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_001
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero ``AUAllOriginal.complete_002 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_002
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.clear_highest_pole ``AUAllOriginal.complete_003 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_003
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.clear_weighted_highest_pole ``AUAllOriginal.complete_004 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_004
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.rising_product ``AUAllOriginal.complete_005 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_005
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.falling_product ``AUAllOriginal.complete_006 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_006
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct_eval ``AUAllOriginal.complete_007 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_007
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.numerator_eval ``AUAllOriginal.complete_008 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_008
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_eq ``AUAllOriginal.complete_009 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_009
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even ``AUAllOriginal.complete_010 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_010
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero ``AUAllOriginal.complete_011 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_011
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer ``AUAllOriginal.complete_012 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_012
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even ``AUAllOriginal.complete_013 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_013
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.local_coordinate_identity ``AUAllOriginal.complete_014 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_014
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate ``AUAllOriginal.complete_015 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_015
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq ``AUAllOriginal.complete_016 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_016
  afCompare "all_original_complete_type_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even ``AUAllOriginal.complete_017 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_017
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.real_factorial_pos ``AUAllOriginal.complete_018 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_018
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_succ ``AUAllOriginal.complete_019 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_019
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper ``AUAllOriginal.complete_020 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_020
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower ``AUAllOriginal.complete_021 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_021
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_lower ``AUAllOriginal.complete_022 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_022
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_upper ``AUAllOriginal.complete_023 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_023
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_pred ``AUAllOriginal.complete_024 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_024
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero ``AUAllOriginal.complete_025 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_025
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.ascending_product_factorial ``AUAllOriginal.complete_026 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_026
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial ``AUAllOriginal.complete_027 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_027
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial ``AUAllOriginal.complete_028 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_028
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial ``AUAllOriginal.complete_029 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_029
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial ``AUAllOriginal.complete_030 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_030
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial_real ``AUAllOriginal.complete_031 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_031
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_pos ``AUAllOriginal.complete_032 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_032
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_real_pos ``AUAllOriginal.complete_033 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_033
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_log_factorial ``AUAllOriginal.complete_034 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_034
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseGap_identity ``AUAllOriginal.complete_035 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_035
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseGap_pos ``AUAllOriginal.complete_036 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_036
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseRatio_pos ``AUAllOriginal.complete_037 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_037
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseRatio_lt_one ``AUAllOriginal.complete_038 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_038
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio ``AUAllOriginal.complete_039 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_039
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseSlope_neg_right ``AUAllOriginal.complete_040 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_040
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift ``AUAllOriginal.complete_041 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_041
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_hasDerivAt ``AUAllOriginal.complete_042 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_042
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.deriv_phase ``AUAllOriginal.complete_043 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_043
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_strictAntiOn_right ``AUAllOriginal.complete_044 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_044
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_le_right_endpoint ``AUAllOriginal.complete_045 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_045
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_pos ``AUAllOriginal.complete_046 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_046
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_eq ``AUAllOriginal.complete_047 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_047
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseRatio_small_interval_le ``AUAllOriginal.complete_048 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_048
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phaseSlope_small_interval_le ``AUAllOriginal.complete_049 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_049
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_one_eq ``AUAllOriginal.complete_050 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_050
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_one ``AUAllOriginal.complete_051 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_051
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt ``AUAllOriginal.complete_052 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_052
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_pos ``AUAllOriginal.complete_053 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_053
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant ``AUAllOriginal.complete_054 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_054
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio ``AUAllOriginal.complete_055 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_055
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos ``AUAllOriginal.complete_056 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_056
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn ``AUAllOriginal.complete_057 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_057
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero ``AUAllOriginal.complete_058 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_058
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.mul_one_add_log_div_le ``AUAllOriginal.complete_059 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_059
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_identity ``AUAllOriginal.complete_060 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_060
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant ``AUAllOriginal.complete_061 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_061
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_global_le_one_add_constant ``AUAllOriginal.complete_062 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_062
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.log_two_lower_rational ``AUAllOriginal.complete_063 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_063
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.log_three_upper_rational ``AUAllOriginal.complete_064 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_064
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational ``AUAllOriginal.complete_065 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_065
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified ``AUAllOriginal.complete_066 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_066
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_global_lt_certified ``AUAllOriginal.complete_067 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_067
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPhase.phase_global_upper_bound ``AUAllOriginal.complete_068 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_068
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalLogBound.scaled_phase_identity ``AUAllOriginal.complete_069 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_069
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase ``AUAllOriginal.complete_070 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_070
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified ``AUAllOriginal.complete_071 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_071
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_le_certified ``AUAllOriginal.complete_072 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_072
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_compact_bound ``AUAllOriginal.complete_073 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_073
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actual_falling_product_le ``AUAllOriginal.complete_074 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_074
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le ``AUAllOriginal.complete_075 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_075
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actual_poleProduct_ge ``AUAllOriginal.complete_076 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_076
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational ``AUAllOriginal.complete_077 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_077
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound ``AUAllOriginal.complete_078 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_078
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticRationalTail.actual_tail_weight_le ``AUAllOriginal.complete_079 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_079
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow ``AUAllOriginal.complete_080 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_080
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable ``AUAllOriginal.complete_081 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_081
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound ``AUAllOriginal.complete_082 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_082
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored ``AUAllOriginal.complete_083 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_083
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le ``AUAllOriginal.complete_084 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_084
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le ``AUAllOriginal.complete_085 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_085
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg ``AUAllOriginal.complete_086 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_086
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg ``AUAllOriginal.complete_087 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_087
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_weight_le ``AUAllOriginal.complete_088 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_088
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound ``AUAllOriginal.complete_089 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_089
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.tailPower_ge ``AUAllOriginal.complete_090 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_090
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg ``AUAllOriginal.complete_091 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_091
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound ``AUAllOriginal.complete_092 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_092
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable ``AUAllOriginal.complete_093 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_093
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable ``AUAllOriginal.complete_094 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_094
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound ``AUAllOriginal.complete_095 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_095
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound ``AUAllOriginal.complete_096 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_096
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail ``AUAllOriginal.complete_097 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_097
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound ``AUAllOriginal.complete_098 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_098
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos ``AUAllOriginal.complete_099 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_099
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le ``AUAllOriginal.complete_100 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_100
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos ``AUAllOriginal.complete_101 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_101
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant ``AUAllOriginal.complete_102 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_102
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity ``AUAllOriginal.complete_103 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_103
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper ``AUAllOriginal.complete_104 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_104
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap ``AUAllOriginal.complete_105 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_105
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound ``AUAllOriginal.complete_106 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_106
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound ``AUAllOriginal.complete_107 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_107
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos ``AUAllOriginal.complete_108 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_108
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound ``AUAllOriginal.complete_109 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_109
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum ``AUAllOriginal.complete_110 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_110
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments ``AUAllOriginal.complete_111 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_111
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_summable ``AUAllOriginal.complete_112 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_112
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable ``AUAllOriginal.complete_113 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_113
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum ``AUAllOriginal.complete_114 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_114
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualMoment_nonneg ``AUAllOriginal.complete_115 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_115
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg ``AUAllOriginal.complete_116 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_116
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound ``AUAllOriginal.complete_117 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_117
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound ``AUAllOriginal.complete_118 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_118
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero ``AUAllOriginal.complete_119 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_119
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent ``AUAllOriginal.complete_120 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_120
  afCompare "all_original_complete_type_compare" ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one ``AUAllOriginal.complete_121 false
  afRecord "all_original_expected_full_proof" ``AUAllOriginal.complete_121
