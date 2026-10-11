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

namespace AUOriginalDefs

def numerator (n : ℕ) (t : ℚ) : ℚ  := 
  (n.factorial : ℚ) ^ 7 *
    (∏ i ∈ range n, (t - ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (t + n + ((i : ℚ) + 1)))

def poleProduct (n : ℕ) (t : ℚ) : ℚ  := 
  ∏ k ∈ range (n + 1), (t + k)

def actualR (n : ℕ) (t : ℚ) : ℚ  :=  ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.poleProduct n t ^ 9

def clearedPoleProduct (n j : ℕ) (t : ℚ) : ℚ  := 
  ∏ k ∈ (range (n + 1)).erase j, (t + k)

def clearedR (n j : ℕ) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.numerator n t / ZetaNine.CoefficientMap.clearedPoleProduct n j t ^ 9

def leadingPoleCoefficient (n j : ℕ) : ℚ  :=  ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ))

def weightedR (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.actualR n t * W.eval (t * (t + n))

def clearedWeightedR (n j : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ  := 
  ZetaNine.CoefficientMap.clearedR n j t * W.eval (t * (t + n))

def weightedLeadingPoleCoefficient (n j : ℕ) (W : ℚ[X]) : ℚ  := 
  ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ))

def phase (x : ℝ) : ℝ  := 
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    (x - 1) * Real.log (x - 1) - 10 * (x + 1) * Real.log (x + 1)

def phaseRatio (x : ℝ) : ℝ  :=  (x + 2) * x ^ 10 / ((x - 1) * (x + 1) ^ 10)

def phaseSlope (x : ℝ) : ℝ  := 
  10 * Real.log x + Real.log (x + 2) - Real.log (x - 1) - 10 * Real.log (x + 1)

def upperSlopeConstant : ℝ  :=  (301 / 100 : ℝ) * (101 / 201 : ℝ) ^ 10

def smoothPhaseGap (x : ℝ) : ℝ  := 
  10 * x * Real.log x + (x + 2) * Real.log (x + 2) -
    10 * (x + 1) * Real.log (x + 1) - ZetaNine.AnalyticPhase.phase 1 -
      (x - 1) * (1 + Real.log ZetaNine.AnalyticPhase.upperSlopeConstant)

def smoothPhaseSlope (x : ℝ) : ℝ  := 
  10 * Real.log x + Real.log (x + 2) - 10 * Real.log (x + 1) -
    Real.log ZetaNine.AnalyticPhase.upperSlopeConstant

def smoothPhaseRatio (x : ℝ) : ℝ  := 
  (x + 2) * (x / (x + 1)) ^ 10

def actualMomentTerm (n r k : ℕ) : ℝ  := 
  (CoefficientMap.actualR n (k : ℚ) : ℝ) *
    ((k : ℝ) * ((k : ℝ) + (n : ℝ))) ^ r

def actualMomentSequence (n r m : ℕ) : ℝ  :=  ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 1)

def actualMoment (n r : ℕ) : ℝ  :=  ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m

def tailPower (n r : ℕ) : ℕ  :=  7 * n + 9 - 2 * r

def tailCoefficient (n r : ℕ) : ℝ  := 
  (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n * (3 / 2 : ℝ) ^ r

def tailWeightConstant (r : ℕ) : ℝ  := 
  (9 / 7 : ℝ) * (3 / 2 : ℝ) ^ r / (2 : ℝ) ^ (9 - 2 * r)

def tailMajorant (n r : ℕ) : ℝ  := 
  ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) /
    (n : ℝ) ^ (2 * r)

def tailExponent : ℝ  :=  7 + 6 * Real.log 2

def momentBoundConstant : ℝ  :=  5184 * Real.exp 18 + (729 / 224 : ℝ) * Real.exp 7

def actualWeightedSequence (n : ℕ) (W : ℚ[X]) (m : ℕ) : ℝ  := 
  (CoefficientMap.weightedR n W ((m + 1 : ℕ) : ℚ) : ℝ)

def weightedCoefficientHeight (n : ℕ) (W : ℚ[X]) : ℝ  := 
  ∑ r ∈ range 5, |(W.coeff r : ℝ)| * (n : ℝ) ^ (2 * r)

def analyticPrefactor (n : ℕ) : ℝ  := 
  ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 * Real.exp (-(2641 / 250 : ℝ) * n)

def uniformError (n : ℕ) : ℝ  := 
  (Real.log ZetaNine.AnalyticUniformMomentBound.momentBoundConstant + 10 * Real.log ((n : ℝ) + 1)) / (n : ℝ)

end AUOriginalDefs

theorem original_value_numerator : AUOriginalDefs.numerator = ZetaNine.CoefficientMap.numerator := rfl
theorem original_value_poleProduct : AUOriginalDefs.poleProduct = ZetaNine.CoefficientMap.poleProduct := rfl
theorem original_value_actualR : AUOriginalDefs.actualR = ZetaNine.CoefficientMap.actualR := rfl
theorem original_value_clearedPoleProduct : AUOriginalDefs.clearedPoleProduct = ZetaNine.CoefficientMap.clearedPoleProduct := rfl
theorem original_value_clearedR : AUOriginalDefs.clearedR = ZetaNine.CoefficientMap.clearedR := rfl
theorem original_value_leadingPoleCoefficient : AUOriginalDefs.leadingPoleCoefficient = ZetaNine.CoefficientMap.leadingPoleCoefficient := rfl
theorem original_value_weightedR : AUOriginalDefs.weightedR = ZetaNine.CoefficientMap.weightedR := rfl
theorem original_value_clearedWeightedR : AUOriginalDefs.clearedWeightedR = ZetaNine.CoefficientMap.clearedWeightedR := rfl
theorem original_value_weightedLeadingPoleCoefficient : AUOriginalDefs.weightedLeadingPoleCoefficient = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient := rfl
theorem original_value_phase : AUOriginalDefs.phase = ZetaNine.AnalyticPhase.phase := rfl
theorem original_value_phaseRatio : AUOriginalDefs.phaseRatio = ZetaNine.AnalyticPhase.phaseRatio := rfl
theorem original_value_phaseSlope : AUOriginalDefs.phaseSlope = ZetaNine.AnalyticPhase.phaseSlope := rfl
theorem original_value_upperSlopeConstant : AUOriginalDefs.upperSlopeConstant = ZetaNine.AnalyticPhase.upperSlopeConstant := rfl
theorem original_value_smoothPhaseGap : AUOriginalDefs.smoothPhaseGap = ZetaNine.AnalyticPhase.smoothPhaseGap := rfl
theorem original_value_smoothPhaseSlope : AUOriginalDefs.smoothPhaseSlope = ZetaNine.AnalyticPhase.smoothPhaseSlope := rfl
theorem original_value_smoothPhaseRatio : AUOriginalDefs.smoothPhaseRatio = ZetaNine.AnalyticPhase.smoothPhaseRatio := rfl
theorem original_value_actualMomentTerm : AUOriginalDefs.actualMomentTerm = ZetaNine.AnalyticMomentBounds.actualMomentTerm := rfl
theorem original_value_actualMomentSequence : AUOriginalDefs.actualMomentSequence = ZetaNine.AnalyticMomentBounds.actualMomentSequence := rfl
theorem original_value_actualMoment : AUOriginalDefs.actualMoment = ZetaNine.AnalyticMomentBounds.actualMoment := rfl
theorem original_value_tailPower : AUOriginalDefs.tailPower = ZetaNine.AnalyticMomentBounds.tailPower := rfl
theorem original_value_tailCoefficient : AUOriginalDefs.tailCoefficient = ZetaNine.AnalyticMomentBounds.tailCoefficient := rfl
theorem original_value_tailWeightConstant : AUOriginalDefs.tailWeightConstant = ZetaNine.AnalyticUniformMomentBound.tailWeightConstant := rfl
theorem original_value_tailMajorant : AUOriginalDefs.tailMajorant = ZetaNine.AnalyticUniformMomentBound.tailMajorant := rfl
theorem original_value_tailExponent : AUOriginalDefs.tailExponent = ZetaNine.AnalyticUniformMomentBound.tailExponent := rfl
theorem original_value_momentBoundConstant : AUOriginalDefs.momentBoundConstant = ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := rfl
theorem original_value_actualWeightedSequence : AUOriginalDefs.actualWeightedSequence = ZetaNine.AnalyticWeightedBound.actualWeightedSequence := rfl
theorem original_value_weightedCoefficientHeight : AUOriginalDefs.weightedCoefficientHeight = ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight := rfl
theorem original_value_analyticPrefactor : AUOriginalDefs.analyticPrefactor = ZetaNine.AnalyticWeightedBound.analyticPrefactor := rfl
theorem original_value_uniformError : AUOriginalDefs.uniformError = ZetaNine.AnalyticWeightedBound.uniformError := rfl

namespace AUExpected

theorem real_factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.real_factorial_pos

theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_succ

theorem log_successor_increment_upper (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper

theorem log_successor_increment_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower

theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_lower

theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := ZetaNine.AnalyticFactorialBounds.log_factorial_upper

theorem log_factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := ZetaNine.AnalyticFactorialBounds.log_factorial_pred

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 := ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero

theorem ascending_product_factorial (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.ascending_product_factorial

theorem actual_falling_product_factorial (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial

theorem actual_rising_product_factorial (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial

theorem actual_poleProduct_factorial (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial

theorem actualR_factorial (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := ZetaNine.AnalyticRationalFactorial.actualR_factorial

theorem actualR_factorial_real (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := ZetaNine.AnalyticRationalFactorial.actualR_factorial_real

theorem actualR_pos (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := ZetaNine.AnalyticRationalFactorial.actualR_pos

theorem actualR_real_pos (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := ZetaNine.AnalyticRationalFactorial.actualR_real_pos

theorem actualR_log_factorial (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := ZetaNine.AnalyticRationalFactorial.actualR_log_factorial

theorem scaled_phase_identity (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := ZetaNine.AnalyticRationalLogBound.scaled_phase_identity

theorem actualR_log_le_phase (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase

theorem actualR_log_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified

theorem actualR_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticRationalLogBound.actualR_le_certified

theorem actualR_compact_bound (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticRationalLogBound.actualR_compact_bound

theorem actual_falling_product_le (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := ZetaNine.AnalyticRationalTail.actual_falling_product_le

theorem actual_rising_product_tail_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le

theorem actual_poleProduct_ge (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := ZetaNine.AnalyticRationalTail.actual_poleProduct_ge

theorem actualR_tail_bound_rational (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational

theorem actualR_tail_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := ZetaNine.AnalyticRationalTail.actualR_tail_bound

theorem actual_tail_weight_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := ZetaNine.AnalyticRationalTail.actual_tail_weight_le

theorem nat_negative_rpow_eq_reciprocal_pow (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow

theorem reciprocal_power_tail_summable (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable

theorem reciprocal_power_tail_bound (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound

theorem reciprocal_power_tail_bound_factored (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored

theorem actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le

theorem actualMomentTerm_zero_of_pos_le (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k = 0 := ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le

theorem actualMomentTerm_nonneg (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k := ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg

theorem actualMomentSequence_nonneg (n r m : ℕ) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg

theorem actual_compact_weight_le (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := ZetaNine.AnalyticMomentBounds.actual_compact_weight_le

theorem actual_compact_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound

theorem tailPower_ge (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ ZetaNine.AnalyticMomentBounds.tailPower n r := ZetaNine.AnalyticMomentBounds.tailPower_ge

theorem tailCoefficient_nonneg (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r := ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg

theorem actual_tail_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (k : ℝ) ^ ZetaNine.AnalyticMomentBounds.tailPower n r := ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound

theorem actualMomentSequence_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (ZetaNine.AnalyticMomentBounds.actualMomentSequence n r) := ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable

theorem actualMomentSequence_norm_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m‖) := ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable

theorem actual_compact_moment_sum_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound

theorem actual_tail_moment_sum_factorial_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound

theorem actualMoment_eq_compact_add_tail (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r = (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) +
      ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n) := ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail

theorem actualMoment_compact_add_factorial_tail_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound

theorem tailWeightConstant_pos (r : ℕ) : 0 < ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r := ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos

theorem tailWeightConstant_le (r : ℕ) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r ≤ (729 / 224 : ℝ) := ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le

theorem tailMajorant_pos (n r : ℕ) (hn : 1 ≤ n) : 0 < ZetaNine.AnalyticUniformMomentBound.tailMajorant n r := ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos

theorem log_tailWeightConstant (r : ℕ) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant

theorem log_tailMajorant_identity (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (ZetaNine.AnalyticMomentBounds.tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity

theorem log_tailMajorant_upper (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) ≤ Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) + 7 -
      ZetaNine.AnalyticUniformMomentBound.tailExponent * n - 2 * Real.log (n : ℝ) := ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper

theorem certified_tailExponent_gap :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < ZetaNine.AnalyticUniformMomentBound.tailExponent := ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap

theorem tailMajorant_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound

theorem actual_tail_moment_sum_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound

theorem momentBoundConstant_pos : 0 < ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos

theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤ ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound

theorem actualWeightedSequence_eq_actual_moment_sum (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum

theorem actualWeighted_hasSum_actual_moments (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r) := ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments

theorem actualWeighted_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W) := ZetaNine.AnalyticWeightedBound.actualWeighted_summable

theorem actualWeighted_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m‖) := ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable

theorem actualWeighted_tsum_eq_actual_moment_sum (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r := ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum

theorem actualMoment_nonneg (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.actualMoment n r := ZetaNine.AnalyticWeightedBound.actualMoment_nonneg

theorem weightedCoefficientHeight_nonneg (n : ℕ) (W : ℚ[X]) :
    0 ≤ ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg

theorem actualWeighted_uniform_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound

theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n (W n) m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n (W n) := ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound

theorem uniformError_tendsto_zero : Tendsto ZetaNine.AnalyticWeightedBound.uniformError atTop (𝓝 0) := ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero

theorem analyticPrefactor_eq_uniform_exponent (n : ℕ) (hn : 1 ≤ n) :
    ZetaNine.AnalyticWeightedBound.analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + ZetaNine.AnalyticWeightedBound.uniformError n) * n) := ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent

theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one

end AUExpected

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
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.numerator ``AUOriginalDefs.numerator true
  afRecord "definition_rfl" ``original_value_numerator
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.poleProduct ``AUOriginalDefs.poleProduct true
  afRecord "definition_rfl" ``original_value_poleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.actualR ``AUOriginalDefs.actualR true
  afRecord "definition_rfl" ``original_value_actualR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct ``AUOriginalDefs.clearedPoleProduct true
  afRecord "definition_rfl" ``original_value_clearedPoleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedR ``AUOriginalDefs.clearedR true
  afRecord "definition_rfl" ``original_value_clearedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient ``AUOriginalDefs.leadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_leadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedR ``AUOriginalDefs.weightedR true
  afRecord "definition_rfl" ``original_value_weightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedWeightedR ``AUOriginalDefs.clearedWeightedR true
  afRecord "definition_rfl" ``original_value_clearedWeightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient ``AUOriginalDefs.weightedLeadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_weightedLeadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phase ``AUOriginalDefs.phase true
  afRecord "definition_rfl" ``original_value_phase
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseRatio ``AUOriginalDefs.phaseRatio true
  afRecord "definition_rfl" ``original_value_phaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseSlope ``AUOriginalDefs.phaseSlope true
  afRecord "definition_rfl" ``original_value_phaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant ``AUOriginalDefs.upperSlopeConstant true
  afRecord "definition_rfl" ``original_value_upperSlopeConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap ``AUOriginalDefs.smoothPhaseGap true
  afRecord "definition_rfl" ``original_value_smoothPhaseGap
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope ``AUOriginalDefs.smoothPhaseSlope true
  afRecord "definition_rfl" ``original_value_smoothPhaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio ``AUOriginalDefs.smoothPhaseRatio true
  afRecord "definition_rfl" ``original_value_smoothPhaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm ``AUOriginalDefs.actualMomentTerm true
  afRecord "definition_rfl" ``original_value_actualMomentTerm
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence ``AUOriginalDefs.actualMomentSequence true
  afRecord "definition_rfl" ``original_value_actualMomentSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment ``AUOriginalDefs.actualMoment true
  afRecord "definition_rfl" ``original_value_actualMoment
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailPower ``AUOriginalDefs.tailPower true
  afRecord "definition_rfl" ``original_value_tailPower
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient ``AUOriginalDefs.tailCoefficient true
  afRecord "definition_rfl" ``original_value_tailCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant ``AUOriginalDefs.tailWeightConstant true
  afRecord "definition_rfl" ``original_value_tailWeightConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant ``AUOriginalDefs.tailMajorant true
  afRecord "definition_rfl" ``original_value_tailMajorant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailExponent ``AUOriginalDefs.tailExponent true
  afRecord "definition_rfl" ``original_value_tailExponent
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant ``AUOriginalDefs.momentBoundConstant true
  afRecord "definition_rfl" ``original_value_momentBoundConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence ``AUOriginalDefs.actualWeightedSequence true
  afRecord "definition_rfl" ``original_value_actualWeightedSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight ``AUOriginalDefs.weightedCoefficientHeight true
  afRecord "definition_rfl" ``original_value_weightedCoefficientHeight
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor ``AUOriginalDefs.analyticPrefactor true
  afRecord "definition_rfl" ``original_value_analyticPrefactor
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.uniformError ``AUOriginalDefs.uniformError true
  afRecord "definition_rfl" ``original_value_uniformError
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.real_factorial_pos ``AUExpected.real_factorial_pos false
  afRecord "expected_theorem_value" ``AUExpected.real_factorial_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_succ ``AUExpected.log_factorial_succ false
  afRecord "expected_theorem_value" ``AUExpected.log_factorial_succ
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper ``AUExpected.log_successor_increment_upper false
  afRecord "expected_theorem_value" ``AUExpected.log_successor_increment_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower ``AUExpected.log_successor_increment_lower false
  afRecord "expected_theorem_value" ``AUExpected.log_successor_increment_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_lower ``AUExpected.log_factorial_lower false
  afRecord "expected_theorem_value" ``AUExpected.log_factorial_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_upper ``AUExpected.log_factorial_upper false
  afRecord "expected_theorem_value" ``AUExpected.log_factorial_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_pred ``AUExpected.log_factorial_pred false
  afRecord "expected_theorem_value" ``AUExpected.log_factorial_pred
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero ``AUExpected.rational_factorial_ne_zero false
  afRecord "expected_theorem_value" ``AUExpected.rational_factorial_ne_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.ascending_product_factorial ``AUExpected.ascending_product_factorial false
  afRecord "expected_theorem_value" ``AUExpected.ascending_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial ``AUExpected.actual_falling_product_factorial false
  afRecord "expected_theorem_value" ``AUExpected.actual_falling_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial ``AUExpected.actual_rising_product_factorial false
  afRecord "expected_theorem_value" ``AUExpected.actual_rising_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial ``AUExpected.actual_poleProduct_factorial false
  afRecord "expected_theorem_value" ``AUExpected.actual_poleProduct_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial ``AUExpected.actualR_factorial false
  afRecord "expected_theorem_value" ``AUExpected.actualR_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial_real ``AUExpected.actualR_factorial_real false
  afRecord "expected_theorem_value" ``AUExpected.actualR_factorial_real
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_pos ``AUExpected.actualR_pos false
  afRecord "expected_theorem_value" ``AUExpected.actualR_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_real_pos ``AUExpected.actualR_real_pos false
  afRecord "expected_theorem_value" ``AUExpected.actualR_real_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_log_factorial ``AUExpected.actualR_log_factorial false
  afRecord "expected_theorem_value" ``AUExpected.actualR_log_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.scaled_phase_identity ``AUExpected.scaled_phase_identity false
  afRecord "expected_theorem_value" ``AUExpected.scaled_phase_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase ``AUExpected.actualR_log_le_phase false
  afRecord "expected_theorem_value" ``AUExpected.actualR_log_le_phase
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified ``AUExpected.actualR_log_le_certified false
  afRecord "expected_theorem_value" ``AUExpected.actualR_log_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_le_certified ``AUExpected.actualR_le_certified false
  afRecord "expected_theorem_value" ``AUExpected.actualR_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_compact_bound ``AUExpected.actualR_compact_bound false
  afRecord "expected_theorem_value" ``AUExpected.actualR_compact_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_falling_product_le ``AUExpected.actual_falling_product_le false
  afRecord "expected_theorem_value" ``AUExpected.actual_falling_product_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le ``AUExpected.actual_rising_product_tail_le false
  afRecord "expected_theorem_value" ``AUExpected.actual_rising_product_tail_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_poleProduct_ge ``AUExpected.actual_poleProduct_ge false
  afRecord "expected_theorem_value" ``AUExpected.actual_poleProduct_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational ``AUExpected.actualR_tail_bound_rational false
  afRecord "expected_theorem_value" ``AUExpected.actualR_tail_bound_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound ``AUExpected.actualR_tail_bound false
  afRecord "expected_theorem_value" ``AUExpected.actualR_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_tail_weight_le ``AUExpected.actual_tail_weight_le false
  afRecord "expected_theorem_value" ``AUExpected.actual_tail_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow ``AUExpected.nat_negative_rpow_eq_reciprocal_pow false
  afRecord "expected_theorem_value" ``AUExpected.nat_negative_rpow_eq_reciprocal_pow
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable ``AUExpected.reciprocal_power_tail_summable false
  afRecord "expected_theorem_value" ``AUExpected.reciprocal_power_tail_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound ``AUExpected.reciprocal_power_tail_bound false
  afRecord "expected_theorem_value" ``AUExpected.reciprocal_power_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored ``AUExpected.reciprocal_power_tail_bound_factored false
  afRecord "expected_theorem_value" ``AUExpected.reciprocal_power_tail_bound_factored
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le ``AUExpected.actualR_zero_of_pos_le false
  afRecord "expected_theorem_value" ``AUExpected.actualR_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le ``AUExpected.actualMomentTerm_zero_of_pos_le false
  afRecord "expected_theorem_value" ``AUExpected.actualMomentTerm_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg ``AUExpected.actualMomentTerm_nonneg false
  afRecord "expected_theorem_value" ``AUExpected.actualMomentTerm_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg ``AUExpected.actualMomentSequence_nonneg false
  afRecord "expected_theorem_value" ``AUExpected.actualMomentSequence_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_weight_le ``AUExpected.actual_compact_weight_le false
  afRecord "expected_theorem_value" ``AUExpected.actual_compact_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound ``AUExpected.actual_compact_momentTerm_bound false
  afRecord "expected_theorem_value" ``AUExpected.actual_compact_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailPower_ge ``AUExpected.tailPower_ge false
  afRecord "expected_theorem_value" ``AUExpected.tailPower_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg ``AUExpected.tailCoefficient_nonneg false
  afRecord "expected_theorem_value" ``AUExpected.tailCoefficient_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound ``AUExpected.actual_tail_momentTerm_bound false
  afRecord "expected_theorem_value" ``AUExpected.actual_tail_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable ``AUExpected.actualMomentSequence_summable false
  afRecord "expected_theorem_value" ``AUExpected.actualMomentSequence_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable ``AUExpected.actualMomentSequence_norm_summable false
  afRecord "expected_theorem_value" ``AUExpected.actualMomentSequence_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound ``AUExpected.actual_compact_moment_sum_bound false
  afRecord "expected_theorem_value" ``AUExpected.actual_compact_moment_sum_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound ``AUExpected.actual_tail_moment_sum_factorial_bound false
  afRecord "expected_theorem_value" ``AUExpected.actual_tail_moment_sum_factorial_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail ``AUExpected.actualMoment_eq_compact_add_tail false
  afRecord "expected_theorem_value" ``AUExpected.actualMoment_eq_compact_add_tail
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound ``AUExpected.actualMoment_compact_add_factorial_tail_bound false
  afRecord "expected_theorem_value" ``AUExpected.actualMoment_compact_add_factorial_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos ``AUExpected.tailWeightConstant_pos false
  afRecord "expected_theorem_value" ``AUExpected.tailWeightConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le ``AUExpected.tailWeightConstant_le false
  afRecord "expected_theorem_value" ``AUExpected.tailWeightConstant_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos ``AUExpected.tailMajorant_pos false
  afRecord "expected_theorem_value" ``AUExpected.tailMajorant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant ``AUExpected.log_tailWeightConstant false
  afRecord "expected_theorem_value" ``AUExpected.log_tailWeightConstant
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity ``AUExpected.log_tailMajorant_identity false
  afRecord "expected_theorem_value" ``AUExpected.log_tailMajorant_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper ``AUExpected.log_tailMajorant_upper false
  afRecord "expected_theorem_value" ``AUExpected.log_tailMajorant_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap ``AUExpected.certified_tailExponent_gap false
  afRecord "expected_theorem_value" ``AUExpected.certified_tailExponent_gap
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound ``AUExpected.tailMajorant_certified_bound false
  afRecord "expected_theorem_value" ``AUExpected.tailMajorant_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound ``AUExpected.actual_tail_moment_sum_certified_bound false
  afRecord "expected_theorem_value" ``AUExpected.actual_tail_moment_sum_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos ``AUExpected.momentBoundConstant_pos false
  afRecord "expected_theorem_value" ``AUExpected.momentBoundConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound ``AUExpected.actualMoment_uniform_bound false
  afRecord "expected_theorem_value" ``AUExpected.actualMoment_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum ``AUExpected.actualWeightedSequence_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``AUExpected.actualWeightedSequence_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments ``AUExpected.actualWeighted_hasSum_actual_moments false
  afRecord "expected_theorem_value" ``AUExpected.actualWeighted_hasSum_actual_moments
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_summable ``AUExpected.actualWeighted_summable false
  afRecord "expected_theorem_value" ``AUExpected.actualWeighted_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable ``AUExpected.actualWeighted_norm_summable false
  afRecord "expected_theorem_value" ``AUExpected.actualWeighted_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum ``AUExpected.actualWeighted_tsum_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``AUExpected.actualWeighted_tsum_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualMoment_nonneg ``AUExpected.actualMoment_nonneg false
  afRecord "expected_theorem_value" ``AUExpected.actualMoment_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg ``AUExpected.weightedCoefficientHeight_nonneg false
  afRecord "expected_theorem_value" ``AUExpected.weightedCoefficientHeight_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound ``AUExpected.actualWeighted_uniform_bound false
  afRecord "expected_theorem_value" ``AUExpected.actualWeighted_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound ``AUExpected.changing_quartics_uniform_bound false
  afRecord "expected_theorem_value" ``AUExpected.changing_quartics_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero ``AUExpected.uniformError_tendsto_zero false
  afRecord "expected_theorem_value" ``AUExpected.uniformError_tendsto_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent ``AUExpected.analyticPrefactor_eq_uniform_exponent false
  afRecord "expected_theorem_value" ``AUExpected.analyticPrefactor_eq_uniform_exponent
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one ``AUExpected.actual_weighted_uniform_o_one false
  afRecord "expected_theorem_value" ``AUExpected.actual_weighted_uniform_o_one
