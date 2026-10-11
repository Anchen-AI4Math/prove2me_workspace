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
  liftIO <| IO.println ("AF_RECORD|" ++ j.compress)

private def afAxioms (n : Name) : MetaM Json := do
  let axs ← Lean.collectAxioms n
  for a in axs do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Outside Std3: {n} -> {a}"
  return toJson (axs.map Name.toString)

private def afRecord (kind : String) (n : Name) : MetaM Unit := do
  let ci ← getConstInfo n
  let mut value := Json.null
  let mut valueTyped := false
  if let some e := ci.value? true then
    value := toJson (reprStr e)
    valueTyped ← isDefEq (← inferType e) ci.type
    unless valueTyped do throwError "Actual value/type kernel mismatch {n}"
  afEmit <| Json.mkObj [("kind",toJson kind),("name",toJson n.toString),
    ("type_raw",toJson (reprStr ci.type)),("value_raw",value),
    ("value_type_isDefEq",toJson valueTyped),
    ("levelParams",toJson (ci.levelParams.map Name.toString)),
    ("isProp",toJson (← isProp ci.type)),("axioms",← afAxioms n)]

namespace AFOriginalDefs
def numerator (n : ℕ) (t : ℚ) : ℚ :=
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))

def poleProduct (n : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ range (n + 1), (t + k)

def actualR (n : ℕ) (t : ℚ) : ℚ := ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.poleProduct n t ^ 9

def clearedPoleProduct (n j : ℕ) (t : ℚ) : ℚ :=
  ∏ k ∈ (range (n + 1)).erase j, (t + k)

def clearedR (n j : ℕ) (t : ℚ) : ℚ :=
  ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.clearedPoleProduct n j t ^ 9

def leadingPoleCoefficient (n j : ℕ) : ℚ := ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ))

def weightedR (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ZetaNine.CoefficientMap.actualR n t * W.eval (t * (t + n))

def clearedWeightedR (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ZetaNine.CoefficientMap.clearedR n j t * W.eval (t * (t + n))

def weightedLeadingPoleCoefficient (n j : ℕ) (W : ℚ[X]) : ℚ :=
  ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ))

def phase (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ := (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ := (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

def smoothPhaseGap (x : ℝ) : ℝ :=
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - ZetaNine.AnalyticPhase.phase 1 -
      (x - 1) * (1 + Real.log ZetaNine.AnalyticPhase.upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ :=
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log ZetaNine.AnalyticPhase.upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ :=
  (x + 2) * (x / (x + 1)) ^ 10

def actualMomentTerm (n r k : ℕ) : ℝ :=
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ := ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ := ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ := 7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ :=
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

def tailWeightConstant (r : ℕ) : ℝ :=
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ :=
  ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ := 7 + 6 * Real.log 2

def momentBoundConstant : ℝ := 5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ :=
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ :=
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ :=
  ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ :=
  (Real.log ZetaNine.AnalyticUniformMomentBound.momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)

end AFOriginalDefs

theorem original_value_numerator : AFOriginalDefs.numerator = ZetaNine.CoefficientMap.numerator := rfl
theorem original_value_poleProduct : AFOriginalDefs.poleProduct = ZetaNine.CoefficientMap.poleProduct := rfl
theorem original_value_actualR : AFOriginalDefs.actualR = ZetaNine.CoefficientMap.actualR := rfl
theorem original_value_clearedPoleProduct : AFOriginalDefs.clearedPoleProduct = ZetaNine.CoefficientMap.clearedPoleProduct := rfl
theorem original_value_clearedR : AFOriginalDefs.clearedR = ZetaNine.CoefficientMap.clearedR := rfl
theorem original_value_leadingPoleCoefficient : AFOriginalDefs.leadingPoleCoefficient = ZetaNine.CoefficientMap.leadingPoleCoefficient := rfl
theorem original_value_weightedR : AFOriginalDefs.weightedR = ZetaNine.CoefficientMap.weightedR := rfl
theorem original_value_clearedWeightedR : AFOriginalDefs.clearedWeightedR = ZetaNine.CoefficientMap.clearedWeightedR := rfl
theorem original_value_weightedLeadingPoleCoefficient : AFOriginalDefs.weightedLeadingPoleCoefficient = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient := rfl
theorem original_value_phase : AFOriginalDefs.phase = ZetaNine.AnalyticPhase.phase := rfl
theorem original_value_phaseRatio : AFOriginalDefs.phaseRatio = ZetaNine.AnalyticPhase.phaseRatio := rfl
theorem original_value_phaseSlope : AFOriginalDefs.phaseSlope = ZetaNine.AnalyticPhase.phaseSlope := rfl
theorem original_value_upperSlopeConstant : AFOriginalDefs.upperSlopeConstant = ZetaNine.AnalyticPhase.upperSlopeConstant := rfl
theorem original_value_smoothPhaseGap : AFOriginalDefs.smoothPhaseGap = ZetaNine.AnalyticPhase.smoothPhaseGap := rfl
theorem original_value_smoothPhaseSlope : AFOriginalDefs.smoothPhaseSlope = ZetaNine.AnalyticPhase.smoothPhaseSlope := rfl
theorem original_value_smoothPhaseRatio : AFOriginalDefs.smoothPhaseRatio = ZetaNine.AnalyticPhase.smoothPhaseRatio := rfl
theorem original_value_actualMomentTerm : AFOriginalDefs.actualMomentTerm = ZetaNine.AnalyticMomentBounds.actualMomentTerm := rfl
theorem original_value_actualMomentSequence : AFOriginalDefs.actualMomentSequence = ZetaNine.AnalyticMomentBounds.actualMomentSequence := rfl
theorem original_value_actualMoment : AFOriginalDefs.actualMoment = ZetaNine.AnalyticMomentBounds.actualMoment := rfl
theorem original_value_tailPower : AFOriginalDefs.tailPower = ZetaNine.AnalyticMomentBounds.tailPower := rfl
theorem original_value_tailCoefficient : AFOriginalDefs.tailCoefficient = ZetaNine.AnalyticMomentBounds.tailCoefficient := rfl
theorem original_value_tailWeightConstant : AFOriginalDefs.tailWeightConstant = ZetaNine.AnalyticUniformMomentBound.tailWeightConstant := rfl
theorem original_value_tailMajorant : AFOriginalDefs.tailMajorant = ZetaNine.AnalyticUniformMomentBound.tailMajorant := rfl
theorem original_value_tailExponent : AFOriginalDefs.tailExponent = ZetaNine.AnalyticUniformMomentBound.tailExponent := rfl
theorem original_value_momentBoundConstant : AFOriginalDefs.momentBoundConstant = ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := rfl
theorem original_value_actualWeightedSequence : AFOriginalDefs.actualWeightedSequence = ZetaNine.AnalyticWeightedBound.actualWeightedSequence := rfl
theorem original_value_weightedCoefficientHeight : AFOriginalDefs.weightedCoefficientHeight = ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight := rfl
theorem original_value_analyticPrefactor : AFOriginalDefs.analyticPrefactor = ZetaNine.AnalyticWeightedBound.analyticPrefactor := rfl
theorem original_value_uniformError : AFOriginalDefs.uniformError = ZetaNine.AnalyticWeightedBound.uniformError := rfl

namespace AFExpected
theorem real_factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by
  exact @ZetaNine.AnalyticFactorialBounds.real_factorial_pos n

theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
  exact @ZetaNine.AnalyticFactorialBounds.log_factorial_succ n

theorem log_successor_increment_upper (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
  exact @ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper n hn

theorem log_successor_increment_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  exact @ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower n hn

theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := by
  exact @ZetaNine.AnalyticFactorialBounds.log_factorial_lower n

theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := by
  exact @ZetaNine.AnalyticFactorialBounds.log_factorial_upper n hn

theorem log_factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := by
  exact @ZetaNine.AnalyticFactorialBounds.log_factorial_pred n hn

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  exact @ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero n

theorem ascending_product_factorial (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := by
  exact @ZetaNine.AnalyticRationalFactorial.ascending_product_factorial a m ha

theorem actual_falling_product_factorial (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial n k hk

theorem actual_rising_product_factorial (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial n k

theorem actual_poleProduct_factorial (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial n k hk

theorem actualR_factorial (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := by
  exact @ZetaNine.AnalyticRationalFactorial.actualR_factorial n k hk

theorem actualR_factorial_real (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := by
  exact @ZetaNine.AnalyticRationalFactorial.actualR_factorial_real n k hk

theorem actualR_pos (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actualR_pos n k hk

theorem actualR_real_pos (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actualR_real_pos n k hk

theorem actualR_log_factorial (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := by
  exact @ZetaNine.AnalyticRationalFactorial.actualR_log_factorial n k hk

theorem scaled_phase_identity (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := by
  exact @ZetaNine.AnalyticRationalLogBound.scaled_phase_identity n k hn hk

theorem actualR_log_le_phase (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  exact @ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase n k hn hk

theorem actualR_log_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  exact @ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified n k hn hk

theorem actualR_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
  exact @ZetaNine.AnalyticRationalLogBound.actualR_le_certified n k hn hk

theorem actualR_compact_bound (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := by
  exact @ZetaNine.AnalyticRationalLogBound.actualR_compact_bound n k hn hk hk2

theorem actual_falling_product_le (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := by
  exact @ZetaNine.AnalyticRationalTail.actual_falling_product_le n k hk

theorem actual_rising_product_tail_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := by
  exact @ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le n k hk

theorem actual_poleProduct_ge (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := by
  exact @ZetaNine.AnalyticRationalTail.actual_poleProduct_ge n k

theorem actualR_tail_bound_rational (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := by
  exact @ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational n k hn hk

theorem actualR_tail_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := by
  exact @ZetaNine.AnalyticRationalTail.actualR_tail_bound n k hn hk

theorem actual_tail_weight_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
  exact @ZetaNine.AnalyticRationalTail.actual_tail_weight_le n k hk

theorem nat_negative_rpow_eq_reciprocal_pow (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := by
  exact @ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow k s

theorem reciprocal_power_tail_summable (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := by
  exact @ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable M s hs

theorem reciprocal_power_tail_bound (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
  exact @ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound M s hM hs

theorem reciprocal_power_tail_bound_factored (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  exact @ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored M s hM hs

theorem actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  exact @ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le n k hk hkn

theorem actualMomentTerm_zero_of_pos_le (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    actualMomentTerm n r k = 0 := by
  exact @ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le n r k hk hkn

theorem actualMomentTerm_nonneg (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ actualMomentTerm n r k := by
  exact @ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg n r k hk

theorem actualMomentSequence_nonneg (n r m : ℕ) :
    0 ≤ actualMomentSequence n r m := by
  exact @ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg n r m

theorem actual_compact_weight_le (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := by
  exact @ZetaNine.AnalyticMomentBounds.actual_compact_weight_le n k hk

theorem actual_compact_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  exact @ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound n r k hn hr hk hk2

theorem tailPower_ge (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ tailPower n r := by
  exact @ZetaNine.AnalyticMomentBounds.tailPower_ge n r hr

theorem tailCoefficient_nonneg (n r : ℕ) : 0 ≤ tailCoefficient n r := by
  exact @ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg n r

theorem actual_tail_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    actualMomentTerm n r k ≤ tailCoefficient n r / (k : ℝ) ^ tailPower n r := by
  exact @ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound n r k hn hr hk

theorem actualMomentSequence_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (actualMomentSequence n r) := by
  exact @ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable n r hn hr

theorem actualMomentSequence_norm_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖actualMomentSequence n r m‖) := by
  exact @ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable n r hn hr

theorem actual_compact_moment_sum_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  exact @ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound n r hn hr

theorem actual_tail_moment_sum_factorial_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  exact @ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound n r hn hr

theorem actualMoment_eq_compact_add_tail (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r = (∑ m ∈ range (2 * n - 1), actualMomentSequence n r m) +
      ∑' m : ℕ, actualMomentTerm n r (m + 2 * n) := by
  exact @ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail n r hn hr

theorem actualMoment_compact_add_factorial_tail_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      tailCoefficient n r / (2 * (n : ℝ)) ^ tailPower n r * (9 / 7 : ℝ) := by
  exact @ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound n r hn hr

theorem tailWeightConstant_pos (r : ℕ) : 0 < tailWeightConstant r := by
  exact @ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos r

theorem tailWeightConstant_le (r : ℕ) (hr : r ≤ 4) :
    tailWeightConstant r ≤ (729 / 224 : ℝ) := by
  exact @ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le r hr

theorem tailMajorant_pos (n r : ℕ) (hn : 1 ≤ n) : 0 < tailMajorant n r := by
  exact @ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos n r hn

theorem log_tailWeightConstant (r : ℕ) :
    Real.log (tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := by
  exact @ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant r

theorem log_tailMajorant_identity (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := by
  exact @ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity n r hn

theorem log_tailMajorant_upper (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (tailMajorant n r) ≤ Real.log (tailWeightConstant r) + 7 -
      tailExponent * n - 2 * Real.log (n : ℝ) := by
  exact @ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper n r hn hr

theorem certified_tailExponent_gap :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < tailExponent := by
  exact @ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap 

theorem tailMajorant_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := by
  exact @ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound n r hn hr

theorem actual_tail_moment_sum_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := by
  exact @ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound n r hn hr

theorem momentBoundConstant_pos : 0 < momentBoundConstant := by
  exact @ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos 

theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    actualMoment n r ≤ momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  exact @ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound n r hn hr

theorem actualWeightedSequence_eq_actual_moment_sum (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMomentSequence n r m := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum n W hW m

theorem actualWeighted_hasSum_actual_moments (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r) := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments n hn W hW

theorem actualWeighted_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (actualWeightedSequence n W) := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeighted_summable n hn W hW

theorem actualWeighted_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖actualWeightedSequence n W m‖) := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable n hn W hW

theorem actualWeighted_tsum_eq_actual_moment_sum (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * actualMoment n r := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum n hn W hW

theorem actualMoment_nonneg (n r : ℕ) : 0 ≤ actualMoment n r := by
  exact @ZetaNine.AnalyticWeightedBound.actualMoment_nonneg n r

theorem weightedCoefficientHeight_nonneg (n : ℕ) (W : ℚ[X]) :
    0 ≤ weightedCoefficientHeight n W := by
  exact @ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg n W

theorem actualWeighted_uniform_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, actualWeightedSequence n W m| ≤
      analyticPrefactor n * weightedCoefficientHeight n W := by
  exact @ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound n hn W hW

theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, actualWeightedSequence n (W n) m| ≤
      analyticPrefactor n * weightedCoefficientHeight n (W n) := by
  exact @ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound W hW

theorem uniformError_tendsto_zero : Tendsto uniformError atTop (𝓝 0) := by
  exact @ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero 

theorem analyticPrefactor_eq_uniform_exponent (n : ℕ) (hn : 1 ≤ n) :
    analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + uniformError n) * n) := by
  exact @ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent n hn

theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * weightedCoefficientHeight n W := by
  exact @ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one 

end AFExpected

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
          ("value_actual_raw",toJson (reprStr va)),("value_expected_raw",toJson (reprStr vb)),
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
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.numerator ``AFOriginalDefs.numerator true
  afRecord "definition_rfl" ``original_value_numerator
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.poleProduct ``AFOriginalDefs.poleProduct true
  afRecord "definition_rfl" ``original_value_poleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.actualR ``AFOriginalDefs.actualR true
  afRecord "definition_rfl" ``original_value_actualR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct ``AFOriginalDefs.clearedPoleProduct true
  afRecord "definition_rfl" ``original_value_clearedPoleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedR ``AFOriginalDefs.clearedR true
  afRecord "definition_rfl" ``original_value_clearedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient ``AFOriginalDefs.leadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_leadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedR ``AFOriginalDefs.weightedR true
  afRecord "definition_rfl" ``original_value_weightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedWeightedR ``AFOriginalDefs.clearedWeightedR true
  afRecord "definition_rfl" ``original_value_clearedWeightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient ``AFOriginalDefs.weightedLeadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_weightedLeadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phase ``AFOriginalDefs.phase true
  afRecord "definition_rfl" ``original_value_phase
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseRatio ``AFOriginalDefs.phaseRatio true
  afRecord "definition_rfl" ``original_value_phaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseSlope ``AFOriginalDefs.phaseSlope true
  afRecord "definition_rfl" ``original_value_phaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant ``AFOriginalDefs.upperSlopeConstant true
  afRecord "definition_rfl" ``original_value_upperSlopeConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap ``AFOriginalDefs.smoothPhaseGap true
  afRecord "definition_rfl" ``original_value_smoothPhaseGap
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope ``AFOriginalDefs.smoothPhaseSlope true
  afRecord "definition_rfl" ``original_value_smoothPhaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio ``AFOriginalDefs.smoothPhaseRatio true
  afRecord "definition_rfl" ``original_value_smoothPhaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm ``AFOriginalDefs.actualMomentTerm true
  afRecord "definition_rfl" ``original_value_actualMomentTerm
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence ``AFOriginalDefs.actualMomentSequence true
  afRecord "definition_rfl" ``original_value_actualMomentSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment ``AFOriginalDefs.actualMoment true
  afRecord "definition_rfl" ``original_value_actualMoment
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailPower ``AFOriginalDefs.tailPower true
  afRecord "definition_rfl" ``original_value_tailPower
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient ``AFOriginalDefs.tailCoefficient true
  afRecord "definition_rfl" ``original_value_tailCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant ``AFOriginalDefs.tailWeightConstant true
  afRecord "definition_rfl" ``original_value_tailWeightConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant ``AFOriginalDefs.tailMajorant true
  afRecord "definition_rfl" ``original_value_tailMajorant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailExponent ``AFOriginalDefs.tailExponent true
  afRecord "definition_rfl" ``original_value_tailExponent
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant ``AFOriginalDefs.momentBoundConstant true
  afRecord "definition_rfl" ``original_value_momentBoundConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence ``AFOriginalDefs.actualWeightedSequence true
  afRecord "definition_rfl" ``original_value_actualWeightedSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight ``AFOriginalDefs.weightedCoefficientHeight true
  afRecord "definition_rfl" ``original_value_weightedCoefficientHeight
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor ``AFOriginalDefs.analyticPrefactor true
  afRecord "definition_rfl" ``original_value_analyticPrefactor
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.uniformError ``AFOriginalDefs.uniformError true
  afRecord "definition_rfl" ``original_value_uniformError
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.real_factorial_pos ``AFExpected.real_factorial_pos false
  afRecord "expected_theorem_value" ``AFExpected.real_factorial_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_succ ``AFExpected.log_factorial_succ false
  afRecord "expected_theorem_value" ``AFExpected.log_factorial_succ
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper ``AFExpected.log_successor_increment_upper false
  afRecord "expected_theorem_value" ``AFExpected.log_successor_increment_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower ``AFExpected.log_successor_increment_lower false
  afRecord "expected_theorem_value" ``AFExpected.log_successor_increment_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_lower ``AFExpected.log_factorial_lower false
  afRecord "expected_theorem_value" ``AFExpected.log_factorial_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_upper ``AFExpected.log_factorial_upper false
  afRecord "expected_theorem_value" ``AFExpected.log_factorial_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_pred ``AFExpected.log_factorial_pred false
  afRecord "expected_theorem_value" ``AFExpected.log_factorial_pred
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero ``AFExpected.rational_factorial_ne_zero false
  afRecord "expected_theorem_value" ``AFExpected.rational_factorial_ne_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.ascending_product_factorial ``AFExpected.ascending_product_factorial false
  afRecord "expected_theorem_value" ``AFExpected.ascending_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial ``AFExpected.actual_falling_product_factorial false
  afRecord "expected_theorem_value" ``AFExpected.actual_falling_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial ``AFExpected.actual_rising_product_factorial false
  afRecord "expected_theorem_value" ``AFExpected.actual_rising_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial ``AFExpected.actual_poleProduct_factorial false
  afRecord "expected_theorem_value" ``AFExpected.actual_poleProduct_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial ``AFExpected.actualR_factorial false
  afRecord "expected_theorem_value" ``AFExpected.actualR_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial_real ``AFExpected.actualR_factorial_real false
  afRecord "expected_theorem_value" ``AFExpected.actualR_factorial_real
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_pos ``AFExpected.actualR_pos false
  afRecord "expected_theorem_value" ``AFExpected.actualR_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_real_pos ``AFExpected.actualR_real_pos false
  afRecord "expected_theorem_value" ``AFExpected.actualR_real_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_log_factorial ``AFExpected.actualR_log_factorial false
  afRecord "expected_theorem_value" ``AFExpected.actualR_log_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.scaled_phase_identity ``AFExpected.scaled_phase_identity false
  afRecord "expected_theorem_value" ``AFExpected.scaled_phase_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase ``AFExpected.actualR_log_le_phase false
  afRecord "expected_theorem_value" ``AFExpected.actualR_log_le_phase
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified ``AFExpected.actualR_log_le_certified false
  afRecord "expected_theorem_value" ``AFExpected.actualR_log_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_le_certified ``AFExpected.actualR_le_certified false
  afRecord "expected_theorem_value" ``AFExpected.actualR_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_compact_bound ``AFExpected.actualR_compact_bound false
  afRecord "expected_theorem_value" ``AFExpected.actualR_compact_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_falling_product_le ``AFExpected.actual_falling_product_le false
  afRecord "expected_theorem_value" ``AFExpected.actual_falling_product_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le ``AFExpected.actual_rising_product_tail_le false
  afRecord "expected_theorem_value" ``AFExpected.actual_rising_product_tail_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_poleProduct_ge ``AFExpected.actual_poleProduct_ge false
  afRecord "expected_theorem_value" ``AFExpected.actual_poleProduct_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational ``AFExpected.actualR_tail_bound_rational false
  afRecord "expected_theorem_value" ``AFExpected.actualR_tail_bound_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound ``AFExpected.actualR_tail_bound false
  afRecord "expected_theorem_value" ``AFExpected.actualR_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_tail_weight_le ``AFExpected.actual_tail_weight_le false
  afRecord "expected_theorem_value" ``AFExpected.actual_tail_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow ``AFExpected.nat_negative_rpow_eq_reciprocal_pow false
  afRecord "expected_theorem_value" ``AFExpected.nat_negative_rpow_eq_reciprocal_pow
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable ``AFExpected.reciprocal_power_tail_summable false
  afRecord "expected_theorem_value" ``AFExpected.reciprocal_power_tail_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound ``AFExpected.reciprocal_power_tail_bound false
  afRecord "expected_theorem_value" ``AFExpected.reciprocal_power_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored ``AFExpected.reciprocal_power_tail_bound_factored false
  afRecord "expected_theorem_value" ``AFExpected.reciprocal_power_tail_bound_factored
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le ``AFExpected.actualR_zero_of_pos_le false
  afRecord "expected_theorem_value" ``AFExpected.actualR_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le ``AFExpected.actualMomentTerm_zero_of_pos_le false
  afRecord "expected_theorem_value" ``AFExpected.actualMomentTerm_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg ``AFExpected.actualMomentTerm_nonneg false
  afRecord "expected_theorem_value" ``AFExpected.actualMomentTerm_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg ``AFExpected.actualMomentSequence_nonneg false
  afRecord "expected_theorem_value" ``AFExpected.actualMomentSequence_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_weight_le ``AFExpected.actual_compact_weight_le false
  afRecord "expected_theorem_value" ``AFExpected.actual_compact_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound ``AFExpected.actual_compact_momentTerm_bound false
  afRecord "expected_theorem_value" ``AFExpected.actual_compact_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailPower_ge ``AFExpected.tailPower_ge false
  afRecord "expected_theorem_value" ``AFExpected.tailPower_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg ``AFExpected.tailCoefficient_nonneg false
  afRecord "expected_theorem_value" ``AFExpected.tailCoefficient_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound ``AFExpected.actual_tail_momentTerm_bound false
  afRecord "expected_theorem_value" ``AFExpected.actual_tail_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable ``AFExpected.actualMomentSequence_summable false
  afRecord "expected_theorem_value" ``AFExpected.actualMomentSequence_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable ``AFExpected.actualMomentSequence_norm_summable false
  afRecord "expected_theorem_value" ``AFExpected.actualMomentSequence_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound ``AFExpected.actual_compact_moment_sum_bound false
  afRecord "expected_theorem_value" ``AFExpected.actual_compact_moment_sum_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound ``AFExpected.actual_tail_moment_sum_factorial_bound false
  afRecord "expected_theorem_value" ``AFExpected.actual_tail_moment_sum_factorial_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail ``AFExpected.actualMoment_eq_compact_add_tail false
  afRecord "expected_theorem_value" ``AFExpected.actualMoment_eq_compact_add_tail
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound ``AFExpected.actualMoment_compact_add_factorial_tail_bound false
  afRecord "expected_theorem_value" ``AFExpected.actualMoment_compact_add_factorial_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos ``AFExpected.tailWeightConstant_pos false
  afRecord "expected_theorem_value" ``AFExpected.tailWeightConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le ``AFExpected.tailWeightConstant_le false
  afRecord "expected_theorem_value" ``AFExpected.tailWeightConstant_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos ``AFExpected.tailMajorant_pos false
  afRecord "expected_theorem_value" ``AFExpected.tailMajorant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant ``AFExpected.log_tailWeightConstant false
  afRecord "expected_theorem_value" ``AFExpected.log_tailWeightConstant
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity ``AFExpected.log_tailMajorant_identity false
  afRecord "expected_theorem_value" ``AFExpected.log_tailMajorant_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper ``AFExpected.log_tailMajorant_upper false
  afRecord "expected_theorem_value" ``AFExpected.log_tailMajorant_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap ``AFExpected.certified_tailExponent_gap false
  afRecord "expected_theorem_value" ``AFExpected.certified_tailExponent_gap
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound ``AFExpected.tailMajorant_certified_bound false
  afRecord "expected_theorem_value" ``AFExpected.tailMajorant_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound ``AFExpected.actual_tail_moment_sum_certified_bound false
  afRecord "expected_theorem_value" ``AFExpected.actual_tail_moment_sum_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos ``AFExpected.momentBoundConstant_pos false
  afRecord "expected_theorem_value" ``AFExpected.momentBoundConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound ``AFExpected.actualMoment_uniform_bound false
  afRecord "expected_theorem_value" ``AFExpected.actualMoment_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum ``AFExpected.actualWeightedSequence_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``AFExpected.actualWeightedSequence_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments ``AFExpected.actualWeighted_hasSum_actual_moments false
  afRecord "expected_theorem_value" ``AFExpected.actualWeighted_hasSum_actual_moments
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_summable ``AFExpected.actualWeighted_summable false
  afRecord "expected_theorem_value" ``AFExpected.actualWeighted_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable ``AFExpected.actualWeighted_norm_summable false
  afRecord "expected_theorem_value" ``AFExpected.actualWeighted_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum ``AFExpected.actualWeighted_tsum_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``AFExpected.actualWeighted_tsum_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualMoment_nonneg ``AFExpected.actualMoment_nonneg false
  afRecord "expected_theorem_value" ``AFExpected.actualMoment_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg ``AFExpected.weightedCoefficientHeight_nonneg false
  afRecord "expected_theorem_value" ``AFExpected.weightedCoefficientHeight_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound ``AFExpected.actualWeighted_uniform_bound false
  afRecord "expected_theorem_value" ``AFExpected.actualWeighted_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound ``AFExpected.changing_quartics_uniform_bound false
  afRecord "expected_theorem_value" ``AFExpected.changing_quartics_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero ``AFExpected.uniformError_tendsto_zero false
  afRecord "expected_theorem_value" ``AFExpected.uniformError_tendsto_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent ``AFExpected.analyticPrefactor_eq_uniform_exponent false
  afRecord "expected_theorem_value" ``AFExpected.analyticPrefactor_eq_uniform_exponent
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one ``AFExpected.actual_weighted_uniform_o_one false
  afRecord "expected_theorem_value" ``AFExpected.actual_weighted_uniform_o_one
