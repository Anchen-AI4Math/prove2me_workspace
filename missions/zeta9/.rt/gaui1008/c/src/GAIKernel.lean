import GAIExprDag
import Solutions.Sol_ZetaNine_AnalyticWeightedBound_changing_quartics_uniform_bound
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
    stdout.putStrLn ("GAI_RECORD|" ++ j.compress)
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

namespace GAIOriginalDefs
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
end GAIOriginalDefs

theorem original_value_numerator : GAIOriginalDefs.numerator = ZetaNine.CoefficientMap.numerator := rfl
theorem original_value_poleProduct : GAIOriginalDefs.poleProduct = ZetaNine.CoefficientMap.poleProduct := rfl
theorem original_value_actualR : GAIOriginalDefs.actualR = ZetaNine.CoefficientMap.actualR := rfl
theorem original_value_clearedPoleProduct : GAIOriginalDefs.clearedPoleProduct = ZetaNine.CoefficientMap.clearedPoleProduct := rfl
theorem original_value_clearedR : GAIOriginalDefs.clearedR = ZetaNine.CoefficientMap.clearedR := rfl
theorem original_value_leadingPoleCoefficient : GAIOriginalDefs.leadingPoleCoefficient = ZetaNine.CoefficientMap.leadingPoleCoefficient := rfl
theorem original_value_weightedR : GAIOriginalDefs.weightedR = ZetaNine.CoefficientMap.weightedR := rfl
theorem original_value_clearedWeightedR : GAIOriginalDefs.clearedWeightedR = ZetaNine.CoefficientMap.clearedWeightedR := rfl
theorem original_value_weightedLeadingPoleCoefficient : GAIOriginalDefs.weightedLeadingPoleCoefficient = ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient := rfl
theorem original_value_phase : GAIOriginalDefs.phase = ZetaNine.AnalyticPhase.phase := rfl
theorem original_value_phaseRatio : GAIOriginalDefs.phaseRatio = ZetaNine.AnalyticPhase.phaseRatio := rfl
theorem original_value_phaseSlope : GAIOriginalDefs.phaseSlope = ZetaNine.AnalyticPhase.phaseSlope := rfl
theorem original_value_upperSlopeConstant : GAIOriginalDefs.upperSlopeConstant = ZetaNine.AnalyticPhase.upperSlopeConstant := rfl
theorem original_value_smoothPhaseGap : GAIOriginalDefs.smoothPhaseGap = ZetaNine.AnalyticPhase.smoothPhaseGap := rfl
theorem original_value_smoothPhaseSlope : GAIOriginalDefs.smoothPhaseSlope = ZetaNine.AnalyticPhase.smoothPhaseSlope := rfl
theorem original_value_smoothPhaseRatio : GAIOriginalDefs.smoothPhaseRatio = ZetaNine.AnalyticPhase.smoothPhaseRatio := rfl
theorem original_value_actualMomentTerm : GAIOriginalDefs.actualMomentTerm = ZetaNine.AnalyticMomentBounds.actualMomentTerm := rfl
theorem original_value_actualMomentSequence : GAIOriginalDefs.actualMomentSequence = ZetaNine.AnalyticMomentBounds.actualMomentSequence := rfl
theorem original_value_actualMoment : GAIOriginalDefs.actualMoment = ZetaNine.AnalyticMomentBounds.actualMoment := rfl
theorem original_value_tailPower : GAIOriginalDefs.tailPower = ZetaNine.AnalyticMomentBounds.tailPower := rfl
theorem original_value_tailCoefficient : GAIOriginalDefs.tailCoefficient = ZetaNine.AnalyticMomentBounds.tailCoefficient := rfl
theorem original_value_tailWeightConstant : GAIOriginalDefs.tailWeightConstant = ZetaNine.AnalyticUniformMomentBound.tailWeightConstant := rfl
theorem original_value_tailMajorant : GAIOriginalDefs.tailMajorant = ZetaNine.AnalyticUniformMomentBound.tailMajorant := rfl
theorem original_value_tailExponent : GAIOriginalDefs.tailExponent = ZetaNine.AnalyticUniformMomentBound.tailExponent := rfl
theorem original_value_momentBoundConstant : GAIOriginalDefs.momentBoundConstant = ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := rfl
theorem original_value_actualWeightedSequence : GAIOriginalDefs.actualWeightedSequence = ZetaNine.AnalyticWeightedBound.actualWeightedSequence := rfl
theorem original_value_weightedCoefficientHeight : GAIOriginalDefs.weightedCoefficientHeight = ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight := rfl
theorem original_value_analyticPrefactor : GAIOriginalDefs.analyticPrefactor = ZetaNine.AnalyticWeightedBound.analyticPrefactor := rfl
theorem original_value_uniformError : GAIOriginalDefs.uniformError = ZetaNine.AnalyticWeightedBound.uniformError := rfl

namespace GAIExpected

theorem poleProduct_factor (n j : ℕ) (hj : j ≤ n) (t : ℚ) :
    ZetaNine.CoefficientMap.poleProduct n t = (t + j) * ZetaNine.CoefficientMap.clearedPoleProduct n j t := by
  apply ZetaNine.CoefficientMap.poleProduct_factor
  all_goals assumption

theorem poleProduct_ne_zero (n : ℕ) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) : ZetaNine.CoefficientMap.poleProduct n t ≠ 0 := by
  apply ZetaNine.CoefficientMap.poleProduct_ne_zero
  all_goals assumption

theorem clearedPoleProduct_ne_zero (n j : ℕ) :
    ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) ≠ 0 := by
  apply ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero
  all_goals assumption

theorem clear_highest_pole (n j : ℕ) (hj : j ≤ n) (t : ℚ)
    (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.actualR n t * (t + j) ^ 9 = ZetaNine.CoefficientMap.clearedR n j t := by
  apply ZetaNine.CoefficientMap.clear_highest_pole
  all_goals assumption

theorem clear_weighted_highest_pole (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (t : ℚ) (ht : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    ZetaNine.CoefficientMap.weightedR n W t * (t + j) ^ 9 = ZetaNine.CoefficientMap.clearedWeightedR n j W t := by
  apply ZetaNine.CoefficientMap.clear_weighted_highest_pole
  all_goals assumption

theorem rising_product (a n : ℕ) :
    (∏ i ∈ range n, ((a : ℚ) + ((i : ℚ) + 1))) =
      (n.factorial : ℚ) * ((a + n).choose n : ℚ) := by
  apply ZetaNine.CoefficientMap.rising_product
  all_goals assumption

theorem falling_product (n : ℕ) :
    (∏ k ∈ range n, ((k : ℚ) - n)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) := by
  apply ZetaNine.CoefficientMap.falling_product
  all_goals assumption

theorem clearedPoleProduct_eval (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.clearedPoleProduct n j (-(j : ℚ)) =
      (-1 : ℚ) ^ j * (j.factorial : ℚ) * ((n - j).factorial : ℚ) := by
  apply ZetaNine.CoefficientMap.clearedPoleProduct_eval
  all_goals assumption

theorem numerator_eval (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.numerator n (-(j : ℚ)) =
      (-1 : ℚ) ^ n * (n.factorial : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  apply ZetaNine.CoefficientMap.numerator_eval
  all_goals assumption

theorem leadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  apply ZetaNine.CoefficientMap.leadingPoleCoefficient_eq
  all_goals assumption

theorem leadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) := by
  apply ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even
  all_goals assumption

theorem leadingPoleCoefficient_ne_zero (n j : ℕ) (hj : j ≤ n) :
    ZetaNine.CoefficientMap.leadingPoleCoefficient n j ≠ 0 := by
  apply ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero
  all_goals assumption

theorem leadingPoleCoefficient_is_integer (n j : ℕ) (hj : j ≤ n) :
    ∃ z : ℤ, ZetaNine.CoefficientMap.leadingPoleCoefficient n j = (z : ℚ) := by
  apply ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer
  all_goals assumption

theorem signed_leadingPoleCoefficient_pos_even (n j : ℕ) (hn : Even n) (hj : j ≤ n) :
    (-1 : ℚ) ^ j * ZetaNine.CoefficientMap.leadingPoleCoefficient n j > 0 := by
  apply ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even
  all_goals assumption

theorem local_coordinate_identity (n j : ℕ) (hj : j ≤ n) (z : ℚ) :
    (-(j : ℚ) + z) * (-(j : ℚ) + z + n) =
      -(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2 := by
  apply ZetaNine.CoefficientMap.local_coordinate_identity
  all_goals assumption

theorem clearedWeightedR_local_coordinate (n j : ℕ) (hj : j ≤ n)
    (W : ℚ[X]) (z : ℚ) :
    ZetaNine.CoefficientMap.clearedWeightedR n j W (-(j : ℚ) + z) =
      ZetaNine.CoefficientMap.clearedR n j (-(j : ℚ) + z) *
        W.eval (-(j : ℚ) * (n - j : ℕ) + ((n : ℚ) - 2 * j) * z + z ^ 2) := by
  apply ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate
  all_goals assumption

theorem weightedLeadingPoleCoefficient_eq (n j : ℕ) (hj : j ≤ n) (W : ℚ[X]) :
    ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ (n + j) * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  apply ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq
  all_goals assumption

theorem weightedLeadingPoleCoefficient_eq_even (n j : ℕ) (hn : Even n)
    (hj : j ≤ n) (W : ℚ[X]) :
    ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient n j W =
      (-1 : ℚ) ^ j * (n.choose j : ℚ) ^ 9 *
        ((n + j).choose n : ℚ) * ((2 * n - j).choose n : ℚ) *
          W.eval (-(j : ℚ) * (n - j : ℕ)) := by
  apply ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even
  all_goals assumption

theorem real_factorial_pos (n : ℕ) : 0 < (n.factorial : ℝ) := by
  apply ZetaNine.AnalyticFactorialBounds.real_factorial_pos
  all_goals assumption

theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) =
      Real.log ((n : ℝ) + 1) + Real.log (n.factorial : ℝ) := by
  apply ZetaNine.AnalyticFactorialBounds.log_factorial_succ
  all_goals assumption

theorem log_successor_increment_upper (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) * (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) ≤ 1 := by
  apply ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper
  all_goals assumption

theorem log_successor_increment_lower (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ ((n : ℝ) + 1) *
      (Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)) := by
  apply ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower
  all_goals assumption

theorem log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log (n : ℝ) - n ≤ Real.log (n.factorial : ℝ) := by
  apply ZetaNine.AnalyticFactorialBounds.log_factorial_lower
  all_goals assumption

theorem log_factorial_upper (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n.factorial : ℝ) ≤
      ((n : ℝ) + 1) * Real.log (n : ℝ) - n + 1 := by
  apply ZetaNine.AnalyticFactorialBounds.log_factorial_upper
  all_goals assumption

theorem log_factorial_pred (n : ℕ) (hn : 1 ≤ n) :
    Real.log ((n - 1).factorial : ℝ) =
      Real.log (n.factorial : ℝ) - Real.log (n : ℝ) := by
  apply ZetaNine.AnalyticFactorialBounds.log_factorial_pred
  all_goals assumption

theorem rational_factorial_ne_zero (n : ℕ) : (n.factorial : ℚ) ≠ 0 := by
  apply ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero
  all_goals assumption

theorem ascending_product_factorial (a m : ℕ) (ha : 1 ≤ a) :
    (∏ i ∈ range m, ((a : ℚ) + (i : ℚ))) =
      ((a + m - 1).factorial : ℚ) / ((a - 1).factorial : ℚ) := by
  apply ZetaNine.AnalyticRationalFactorial.ascending_product_factorial
  all_goals assumption

theorem actual_falling_product_factorial (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) =
      ((k - 1).factorial : ℚ) / ((k - n - 1).factorial : ℚ) := by
  apply ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial
  all_goals assumption

theorem actual_rising_product_factorial (n k : ℕ) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) =
      ((k + 2 * n).factorial : ℚ) / ((k + n).factorial : ℚ) := by
  apply ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial
  all_goals assumption

theorem actual_poleProduct_factorial (n k : ℕ) (hk : 1 ≤ k) :
    CoefficientMap.poleProduct n (k : ℚ) =
      ((k + n).factorial : ℚ) / ((k - 1).factorial : ℚ) := by
  apply ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial
  all_goals assumption

theorem actualR_factorial (n k : ℕ) (hk : n < k) :
    CoefficientMap.actualR n (k : ℚ) =
      (n.factorial : ℚ) ^ 7 * ((k - 1).factorial : ℚ) ^ 10 *
        ((k + 2 * n).factorial : ℚ) /
      (((k - n - 1).factorial : ℚ) * ((k + n).factorial : ℚ) ^ 10) := by
  apply ZetaNine.AnalyticRationalFactorial.actualR_factorial
  all_goals assumption

theorem actualR_factorial_real (n k : ℕ) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      (n.factorial : ℝ) ^ 7 * ((k - 1).factorial : ℝ) ^ 10 *
        ((k + 2 * n).factorial : ℝ) /
      (((k - n - 1).factorial : ℝ) * ((k + n).factorial : ℝ) ^ 10) := by
  apply ZetaNine.AnalyticRationalFactorial.actualR_factorial_real
  all_goals assumption

theorem actualR_pos (n k : ℕ) (hk : n < k) :
    0 < CoefficientMap.actualR n (k : ℚ) := by
  apply ZetaNine.AnalyticRationalFactorial.actualR_pos
  all_goals assumption

theorem actualR_real_pos (n k : ℕ) (hk : n < k) :
    0 < (CoefficientMap.actualR n (k : ℚ) : ℝ) := by
  apply ZetaNine.AnalyticRationalFactorial.actualR_real_pos
  all_goals assumption

theorem actualR_log_factorial (n k : ℕ) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) =
      7 * Real.log (n.factorial : ℝ) + 10 * Real.log (k.factorial : ℝ) +
        Real.log ((k + 2 * n).factorial : ℝ) -
        Real.log ((k - n).factorial : ℝ) -
        10 * Real.log ((k + n).factorial : ℝ) -
        10 * Real.log (k : ℝ) + Real.log ((k - n : ℕ) : ℝ) := by
  apply ZetaNine.AnalyticRationalFactorial.actualR_log_factorial
  all_goals assumption

theorem phaseGap_identity (x : ℝ) :
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
    (7 / 1 : ℝ) * (x - (101 / 100 : ℝ)) ^ 10 := by
  apply ZetaNine.AnalyticPhase.phaseGap_identity
  all_goals assumption

theorem phaseGap_pos (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    0 < (x - 1) * (x + 1) ^ 10 - (x + 2) * x ^ 10 := by
  apply ZetaNine.AnalyticPhase.phaseGap_pos
  all_goals assumption

theorem phaseRatio_pos (x : ℝ) (hx : 1 < x) : 0 < ZetaNine.AnalyticPhase.phaseRatio x := by
  apply ZetaNine.AnalyticPhase.phaseRatio_pos
  all_goals assumption

theorem phaseRatio_lt_one (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phaseRatio x < 1 := by
  apply ZetaNine.AnalyticPhase.phaseRatio_lt_one
  all_goals assumption

theorem phaseSlope_eq_log_ratio (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phaseSlope x = Real.log (ZetaNine.AnalyticPhase.phaseRatio x) := by
  apply ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio
  all_goals assumption

theorem phaseSlope_neg_right (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phaseSlope x < 0 := by
  apply ZetaNine.AnalyticPhase.phaseSlope_neg_right
  all_goals assumption

theorem hasDerivAt_mul_log_shift (x a : ℝ) (ha : x + a ≠ 0) :
    HasDerivAt (fun y : ℝ => (y + a) * Real.log (y + a))
      (Real.log (x + a) + 1) x := by
  apply ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift
  all_goals assumption

theorem phase_hasDerivAt (x : ℝ) (hx : 1 < x) :
    HasDerivAt ZetaNine.AnalyticPhase.phase (ZetaNine.AnalyticPhase.phaseSlope x) x := by
  apply ZetaNine.AnalyticPhase.phase_hasDerivAt
  all_goals assumption

theorem deriv_phase (x : ℝ) (hx : 1 < x) : deriv ZetaNine.AnalyticPhase.phase x = ZetaNine.AnalyticPhase.phaseSlope x := by
  apply ZetaNine.AnalyticPhase.deriv_phase
  all_goals assumption

theorem phase_strictAntiOn_right : StrictAntiOn ZetaNine.AnalyticPhase.phase (Ici (101 / 100 : ℝ)) := by
  apply ZetaNine.AnalyticPhase.phase_strictAntiOn_right
  all_goals assumption

theorem phase_le_right_endpoint (x : ℝ) (hx : (101 / 100 : ℝ) ≤ x) :
    ZetaNine.AnalyticPhase.phase x ≤ ZetaNine.AnalyticPhase.phase (101 / 100) := by
  apply ZetaNine.AnalyticPhase.phase_le_right_endpoint
  all_goals assumption

theorem upperSlopeConstant_pos : 0 < ZetaNine.AnalyticPhase.upperSlopeConstant := by
  apply ZetaNine.AnalyticPhase.upperSlopeConstant_pos
  all_goals assumption

theorem upperSlopeConstant_eq : ZetaNine.AnalyticPhase.upperSlopeConstant =
    (33249125974877255751301 / 10763674952097696180200100 : ℝ) := by
  apply ZetaNine.AnalyticPhase.upperSlopeConstant_eq
  all_goals assumption

theorem phaseRatio_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : ZetaNine.AnalyticPhase.phaseRatio (1 + u) ≤ ZetaNine.AnalyticPhase.upperSlopeConstant / u := by
  apply ZetaNine.AnalyticPhase.phaseRatio_small_interval_le
  all_goals assumption

theorem phaseSlope_small_interval_le (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) : ZetaNine.AnalyticPhase.phaseSlope (1 + u) ≤ Real.log (ZetaNine.AnalyticPhase.upperSlopeConstant / u) := by
  apply ZetaNine.AnalyticPhase.phaseSlope_small_interval_le
  all_goals assumption

theorem phase_one_eq : ZetaNine.AnalyticPhase.phase 1 = 3 * Real.log 3 - 20 * Real.log 2 := by
  apply ZetaNine.AnalyticPhase.phase_one_eq
  all_goals assumption

theorem smoothPhaseGap_one : ZetaNine.AnalyticPhase.smoothPhaseGap 1 = 0 := by
  apply ZetaNine.AnalyticPhase.smoothPhaseGap_one
  all_goals assumption

theorem smoothPhaseGap_hasDerivAt (x : ℝ) (hx : 1 ≤ x) :
    HasDerivAt ZetaNine.AnalyticPhase.smoothPhaseGap (ZetaNine.AnalyticPhase.smoothPhaseSlope x) x := by
  apply ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt
  all_goals assumption

theorem smoothPhaseRatio_pos (x : ℝ) (hx : 1 ≤ x) :
    0 < ZetaNine.AnalyticPhase.smoothPhaseRatio x := by
  apply ZetaNine.AnalyticPhase.smoothPhaseRatio_pos
  all_goals assumption

theorem smoothPhaseRatio_le_upperSlopeConstant (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseRatio x ≤ ZetaNine.AnalyticPhase.upperSlopeConstant := by
  apply ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant
  all_goals assumption

theorem smoothPhaseSlope_eq_log_ratio (x : ℝ) (hx : 1 ≤ x) :
    ZetaNine.AnalyticPhase.smoothPhaseSlope x =
      Real.log (ZetaNine.AnalyticPhase.smoothPhaseRatio x) - Real.log ZetaNine.AnalyticPhase.upperSlopeConstant := by
  apply ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio
  all_goals assumption

theorem smoothPhaseSlope_nonpos (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseSlope x ≤ 0 := by
  apply ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos
  all_goals assumption

theorem smoothPhaseGap_antitoneOn :
    AntitoneOn ZetaNine.AnalyticPhase.smoothPhaseGap (Icc (1 : ℝ) (101 / 100 : ℝ)) := by
  apply ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn
  all_goals assumption

theorem smoothPhaseGap_le_zero (x : ℝ)
    (hx : x ∈ Icc (1 : ℝ) (101 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.smoothPhaseGap x ≤ 0 := by
  apply ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero
  all_goals assumption

theorem mul_one_add_log_div_le (a u : ℝ) (ha : 0 < a) (hu : 0 < u) :
    u * (1 + Real.log (a / u)) ≤ a := by
  apply ZetaNine.AnalyticPhase.mul_one_add_log_div_le
  all_goals assumption

theorem phase_small_interval_identity (u : ℝ) (hu : 0 < u) :
    ZetaNine.AnalyticPhase.phase (1 + u) = ZetaNine.AnalyticPhase.phase 1 +
      u * (1 + Real.log (ZetaNine.AnalyticPhase.upperSlopeConstant / u)) + ZetaNine.AnalyticPhase.smoothPhaseGap (1 + u) := by
  apply ZetaNine.AnalyticPhase.phase_small_interval_identity
  all_goals assumption

theorem phase_small_interval_le_one_add_constant (u : ℝ) (hu : 0 < u)
    (hu1 : u ≤ (1 / 100 : ℝ)) :
    ZetaNine.AnalyticPhase.phase (1 + u) ≤ ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant := by
  apply ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant
  all_goals assumption

theorem phase_global_le_one_add_constant (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phase x ≤ ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant := by
  apply ZetaNine.AnalyticPhase.phase_global_le_one_add_constant
  all_goals assumption

theorem log_two_lower_rational : (693147 / 1000000 : ℝ) < Real.log 2 := by
  apply ZetaNine.AnalyticPhase.log_two_lower_rational
  all_goals assumption

theorem log_three_upper_rational : Real.log 3 < (1098613 / 1000000 : ℝ) := by
  apply ZetaNine.AnalyticPhase.log_three_upper_rational
  all_goals assumption

theorem upperSlopeConstant_lt_rational :
    ZetaNine.AnalyticPhase.upperSlopeConstant < (309 / 100000 : ℝ) := by
  apply ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational
  all_goals assumption

theorem phase_one_add_constant_lt_certified :
    ZetaNine.AnalyticPhase.phase 1 + ZetaNine.AnalyticPhase.upperSlopeConstant < (-10564011 / 1000000 : ℝ) := by
  apply ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified
  all_goals assumption

theorem phase_global_lt_certified (x : ℝ) (hx : 1 < x) :
    ZetaNine.AnalyticPhase.phase x < (-10564011 / 1000000 : ℝ) := by
  apply ZetaNine.AnalyticPhase.phase_global_lt_certified
  all_goals assumption

theorem phase_global_upper_bound :
    ∀ x : ℝ, 1 < x → ZetaNine.AnalyticPhase.phase x ≤ (-2641 / 250 : ℝ) := by
  apply ZetaNine.AnalyticPhase.phase_global_upper_bound
  all_goals assumption

theorem scaled_phase_identity (n k : ℝ) (hn : 0 < n) (hk : n < k) :
    7 * n * Real.log n + 10 * k * Real.log k +
      (k + 2 * n) * Real.log (k + 2 * n) -
      (k - n) * Real.log (k - n) -
      10 * (k + n) * Real.log (k + n) =
      n * AnalyticPhase.phase (k / n) := by
  apply ZetaNine.AnalyticRationalLogBound.scaled_phase_identity
  all_goals assumption

theorem actualR_log_le_phase (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n : ℝ) * AnalyticPhase.phase ((k : ℝ) / (n : ℝ)) +
        7 * Real.log (n : ℝ) + Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  apply ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase
  all_goals assumption

theorem actualR_log_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    Real.log (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      -(2641 / 250 : ℝ) * n + 7 * Real.log (n : ℝ) +
        Real.log ((k : ℝ) + 2 * (n : ℝ)) +
        Real.log ((k : ℝ) - (n : ℝ)) + 18 := by
  apply ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified
  all_goals assumption

theorem actualR_le_certified (n k : ℕ) (hn : 1 ≤ n) (hk : n < k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      Real.exp 18 * (n : ℝ) ^ 7 * ((k : ℝ) + 2 * (n : ℝ)) *
        ((k : ℝ) - (n : ℝ)) * Real.exp (-(2641 / 250 : ℝ) * n) := by
  apply ZetaNine.AnalyticRationalLogBound.actualR_le_certified
  all_goals assumption

theorem actualR_compact_bound (n k : ℕ) (hn : 1 ≤ n)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      4 * Real.exp 18 * (n : ℝ) ^ 9 * Real.exp (-(2641 / 250 : ℝ) * n) := by
  apply ZetaNine.AnalyticRationalLogBound.actualR_compact_bound
  all_goals assumption

theorem actual_falling_product_le (n k : ℕ) (hk : n < k) :
    (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) ≤ (k : ℚ) ^ n := by
  apply ZetaNine.AnalyticRationalTail.actual_falling_product_le
  all_goals assumption

theorem actual_rising_product_tail_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (∏ i ∈ range n, ((k : ℚ) + (n : ℚ) + ((i : ℚ) + 1))) ≤
      (2 * (k : ℚ)) ^ n := by
  apply ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le
  all_goals assumption

theorem actual_poleProduct_ge (n k : ℕ) :
    (k : ℚ) ^ (n + 1) ≤ CoefficientMap.poleProduct n (k : ℚ) := by
  apply ZetaNine.AnalyticRationalTail.actual_poleProduct_ge
  all_goals assumption

theorem actualR_tail_bound_rational (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    CoefficientMap.actualR n (k : ℚ) ≤
      (n.factorial : ℚ) ^ 7 * (2 : ℚ) ^ n / (k : ℚ) ^ (7 * n + 9) := by
  apply ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational
  all_goals assumption

theorem actualR_tail_bound (n k : ℕ) (hn : 1 ≤ n) (hk : 2 * n ≤ k) :
    (CoefficientMap.actualR n (k : ℚ) : ℝ) ≤
      (n.factorial : ℝ) ^ 7 * (2 : ℝ) ^ n / (k : ℝ) ^ (7 * n + 9) := by
  apply ZetaNine.AnalyticRationalTail.actualR_tail_bound
  all_goals assumption

theorem actual_tail_weight_le (n k : ℕ) (hk : 2 * n ≤ k) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ (3 / 2 : ℝ) * (k : ℝ) ^ 2 := by
  apply ZetaNine.AnalyticRationalTail.actual_tail_weight_le
  all_goals assumption

theorem nat_negative_rpow_eq_reciprocal_pow (k s : ℕ) :
    (k : ℝ) ^ (-(s : ℝ)) = 1 / (k : ℝ) ^ s := by
  apply ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow
  all_goals assumption

theorem reciprocal_power_tail_summable (M s : ℕ) (hs : 2 ≤ s) :
    Summable (fun i : ℕ => 1 / ((i + M : ℕ) : ℝ) ^ s) := by
  apply ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable
  all_goals assumption

theorem reciprocal_power_tail_bound (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s + 1 / (M : ℝ) ^ (s - 1) / ((s - 1 : ℕ) : ℝ) := by
  apply ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound
  all_goals assumption

theorem reciprocal_power_tail_bound_factored (M s : ℕ) (hM : 1 ≤ M) (hs : 2 ≤ s) :
    (∑' i : ℕ, 1 / ((i + M : ℕ) : ℝ) ^ s) ≤
      1 / (M : ℝ) ^ s * (1 + (M : ℝ) / ((s - 1 : ℕ) : ℝ)) := by
  apply ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored
  all_goals assumption

theorem actualR_zero_of_pos_le (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.actualR n (k : ℚ) = 0 := by
  apply ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le
  all_goals assumption

theorem actualMomentTerm_zero_of_pos_le (n r k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k = 0 := by
  apply ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le
  all_goals assumption

theorem actualMomentTerm_nonneg (n r k : ℕ) (hk : 1 ≤ k) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k := by
  apply ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg
  all_goals assumption

theorem actualMomentSequence_nonneg (n r m : ℕ) :
    0 ≤ ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := by
  apply ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg
  all_goals assumption

theorem actual_compact_weight_le (n k : ℕ) (hk : k ≤ 2 * n) :
    (k : ℝ) * ((k : ℝ) + (n : ℝ)) ≤ 6 * (n : ℝ) ^ 2 := by
  apply ZetaNine.AnalyticMomentBounds.actual_compact_weight_le
  all_goals assumption

theorem actual_compact_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : n < k) (hk2 : k ≤ 2 * n) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 9 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  apply ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound
  all_goals assumption

theorem tailPower_ge (n r : ℕ) (hr : r ≤ 4) :
    7 * n + 1 ≤ ZetaNine.AnalyticMomentBounds.tailPower n r := by
  apply ZetaNine.AnalyticMomentBounds.tailPower_ge
  all_goals assumption

theorem tailCoefficient_nonneg (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r := by
  apply ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg
  all_goals assumption

theorem actual_tail_momentTerm_bound (n r k : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4)
    (hk : 2 * n ≤ k) :
    ZetaNine.AnalyticMomentBounds.actualMomentTerm n r k ≤ ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (k : ℝ) ^ ZetaNine.AnalyticMomentBounds.tailPower n r := by
  apply ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound
  all_goals assumption

theorem actualMomentSequence_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (ZetaNine.AnalyticMomentBounds.actualMomentSequence n r) := by
  apply ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable
  all_goals assumption

theorem actualMomentSequence_norm_summable (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m‖) := by
  apply ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable
  all_goals assumption

theorem actual_compact_moment_sum_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) := by
  apply ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound
  all_goals assumption

theorem actual_tail_moment_sum_factorial_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := by
  apply ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound
  all_goals assumption

theorem actualMoment_eq_compact_add_tail (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r = (∑ m ∈ range (2 * n - 1), ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m) +
      ∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n) := by
  apply ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail
  all_goals assumption

theorem actualMoment_compact_add_factorial_tail_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤
      5184 * Real.exp 18 * (n : ℝ) ^ 10 * (n : ℝ) ^ (2 * r) *
        Real.exp (-(2641 / 250 : ℝ) * n) +
      ZetaNine.AnalyticMomentBounds.tailCoefficient n r / (2 * (n : ℝ)) ^ ZetaNine.AnalyticMomentBounds.tailPower n r * (9 / 7 : ℝ) := by
  apply ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound
  all_goals assumption

theorem tailWeightConstant_pos (r : ℕ) : 0 < ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r := by
  apply ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos
  all_goals assumption

theorem tailWeightConstant_le (r : ℕ) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r ≤ (729 / 224 : ℝ) := by
  apply ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le
  all_goals assumption

theorem tailMajorant_pos (n r : ℕ) (hn : 1 ≤ n) : 0 < ZetaNine.AnalyticUniformMomentBound.tailMajorant n r := by
  apply ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos
  all_goals assumption

theorem log_tailWeightConstant (r : ℕ) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) = Real.log (9 / 7 : ℝ) +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      ((9 - 2 * r : ℕ) : ℝ) * Real.log 2 := by
  apply ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant
  all_goals assumption

theorem log_tailMajorant_identity (n r : ℕ) (hn : 1 ≤ n) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) =
      7 * Real.log (n.factorial : ℝ) + (n : ℝ) * Real.log 2 +
      (r : ℝ) * Real.log (3 / 2 : ℝ) -
      (ZetaNine.AnalyticMomentBounds.tailPower n r : ℝ) * (Real.log 2 + Real.log (n : ℝ)) +
      Real.log (9 / 7 : ℝ) - ((2 * r : ℕ) : ℝ) * Real.log (n : ℝ) := by
  apply ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity
  all_goals assumption

theorem log_tailMajorant_upper (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    Real.log (ZetaNine.AnalyticUniformMomentBound.tailMajorant n r) ≤ Real.log (ZetaNine.AnalyticUniformMomentBound.tailWeightConstant r) + 7 -
      ZetaNine.AnalyticUniformMomentBound.tailExponent * n - 2 * Real.log (n : ℝ) := by
  apply ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper
  all_goals assumption

theorem certified_tailExponent_gap :
    (2641 / 250 : ℝ) + (297441 / 500000 : ℝ) < ZetaNine.AnalyticUniformMomentBound.tailExponent := by
  apply ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap
  all_goals assumption

theorem tailMajorant_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticUniformMomentBound.tailMajorant n r ≤ (729 / 224 : ℝ) * Real.exp 7 *
      Real.exp (-(2641 / 250 : ℝ) * n) := by
  apply ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound
  all_goals assumption

theorem actual_tail_moment_sum_certified_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticMomentBounds.actualMomentTerm n r (m + 2 * n)) ≤
      (729 / 224 : ℝ) * Real.exp 7 * Real.exp (-(2641 / 250 : ℝ) * n) *
        (n : ℝ) ^ (2 * r) := by
  apply ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound
  all_goals assumption

theorem momentBoundConstant_pos : 0 < ZetaNine.AnalyticUniformMomentBound.momentBoundConstant := by
  apply ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos
  all_goals assumption

theorem actualMoment_uniform_bound (n r : ℕ) (hn : 1 ≤ n) (hr : r ≤ 4) :
    ZetaNine.AnalyticMomentBounds.actualMoment n r ≤ ZetaNine.AnalyticUniformMomentBound.momentBoundConstant * ((n : ℝ) + 1) ^ 10 *
      Real.exp (-(2641 / 250 : ℝ) * n) * (n : ℝ) ^ (2 * r) := by
  apply ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound
  all_goals assumption

theorem actualWeightedSequence_eq_actual_moment_sum (n : ℕ) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) (m : ℕ) :
    ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMomentSequence n r m := by
  apply ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum
  all_goals assumption

theorem actualWeighted_hasSum_actual_moments (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    HasSum (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W)
      (∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r) := by
  apply ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments
  all_goals assumption

theorem actualWeighted_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X]) (hW : W.natDegree ≤ 4) :
    Summable (ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W) := by
  apply ZetaNine.AnalyticWeightedBound.actualWeighted_summable
  all_goals assumption

theorem actualWeighted_norm_summable (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    Summable (fun m : ℕ => ‖ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m‖) := by
  apply ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable
  all_goals assumption

theorem actualWeighted_tsum_eq_actual_moment_sum (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    (∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m) =
      ∑ r ∈ range 5, (W.coeff r : ℝ) * ZetaNine.AnalyticMomentBounds.actualMoment n r := by
  apply ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum
  all_goals assumption

theorem actualMoment_nonneg (n r : ℕ) : 0 ≤ ZetaNine.AnalyticMomentBounds.actualMoment n r := by
  apply ZetaNine.AnalyticWeightedBound.actualMoment_nonneg
  all_goals assumption

theorem weightedCoefficientHeight_nonneg (n : ℕ) (W : ℚ[X]) :
    0 ≤ ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := by
  apply ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg
  all_goals assumption

theorem actualWeighted_uniform_bound (n : ℕ) (hn : 1 ≤ n) (W : ℚ[X])
    (hW : W.natDegree ≤ 4) :
    |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := by
  apply ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound
  all_goals assumption

theorem changing_quartics_uniform_bound (W : ℕ → ℚ[X])
    (hW : ∀ n : ℕ, (W n).natDegree ≤ 4) :
    ∀ n : ℕ, 1 ≤ n → |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n (W n) m| ≤
      ZetaNine.AnalyticWeightedBound.analyticPrefactor n * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n (W n) := by
  apply ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound
  all_goals assumption

theorem uniformError_tendsto_zero : Tendsto ZetaNine.AnalyticWeightedBound.uniformError atTop (𝓝 0) := by
  apply ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero
  all_goals assumption

theorem analyticPrefactor_eq_uniform_exponent (n : ℕ) (hn : 1 ≤ n) :
    ZetaNine.AnalyticWeightedBound.analyticPrefactor n = Real.exp ((-(2641 / 250 : ℝ) + ZetaNine.AnalyticWeightedBound.uniformError n) * n) := by
  apply ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent
  all_goals assumption

theorem actual_weighted_uniform_o_one :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ W : ℚ[X], W.natDegree ≤ 4 →
        |∑' m : ℕ, ZetaNine.AnalyticWeightedBound.actualWeightedSequence n W m| ≤
          Real.exp ((-(2641 / 250 : ℝ) + ε n) * n) * ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight n W := by
  apply ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one
  all_goals assumption

end GAIExpected

private def afProofHelpers (actual expected : Name) (av bv : Expr) : MetaM (Expr × Expr) := do
  let mut aa := av
  let mut bb := bv
  for _ in [:16] do
    let mut amap : Array (Name × Expr) := #[]
    let mut bmap : Array (Name × Expr) := #[]
    for n in aa.getUsedConstants do
      if #[`ZetaNine.CoefficientMap.numerator, `ZetaNine.CoefficientMap.poleProduct, `ZetaNine.CoefficientMap.actualR, `ZetaNine.CoefficientMap.clearedPoleProduct, `ZetaNine.CoefficientMap.clearedR, `ZetaNine.CoefficientMap.leadingPoleCoefficient, `ZetaNine.CoefficientMap.weightedR, `ZetaNine.CoefficientMap.clearedWeightedR, `ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient, `ZetaNine.AnalyticPhase.phase, `ZetaNine.AnalyticPhase.phaseRatio, `ZetaNine.AnalyticPhase.phaseSlope, `ZetaNine.AnalyticPhase.upperSlopeConstant, `ZetaNine.AnalyticPhase.smoothPhaseGap, `ZetaNine.AnalyticPhase.smoothPhaseSlope, `ZetaNine.AnalyticPhase.smoothPhaseRatio, `ZetaNine.AnalyticMomentBounds.actualMomentTerm, `ZetaNine.AnalyticMomentBounds.actualMomentSequence, `ZetaNine.AnalyticMomentBounds.actualMoment, `ZetaNine.AnalyticMomentBounds.tailPower, `ZetaNine.AnalyticMomentBounds.tailCoefficient, `ZetaNine.AnalyticUniformMomentBound.tailWeightConstant, `ZetaNine.AnalyticUniformMomentBound.tailMajorant, `ZetaNine.AnalyticUniformMomentBound.tailExponent, `ZetaNine.AnalyticUniformMomentBound.momentBoundConstant, `ZetaNine.AnalyticWeightedBound.actualWeightedSequence, `ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight, `ZetaNine.AnalyticWeightedBound.analyticPrefactor, `ZetaNine.AnalyticWeightedBound.uniformError].contains n.getPrefix && n.getString!.startsWith "_proof_" then
        let a ← getConstInfo n
        let some va0 := a.value? true | throwError "Missing actual helper proof {n}"
        let mut matched : Option Name := none
        for m in bb.getUsedConstants do
          if #[`GAIOriginalDefs.numerator, `GAIOriginalDefs.poleProduct, `GAIOriginalDefs.actualR, `GAIOriginalDefs.clearedPoleProduct, `GAIOriginalDefs.clearedR, `GAIOriginalDefs.leadingPoleCoefficient, `GAIOriginalDefs.weightedR, `GAIOriginalDefs.clearedWeightedR, `GAIOriginalDefs.weightedLeadingPoleCoefficient, `GAIOriginalDefs.phase, `GAIOriginalDefs.phaseRatio, `GAIOriginalDefs.phaseSlope, `GAIOriginalDefs.upperSlopeConstant, `GAIOriginalDefs.smoothPhaseGap, `GAIOriginalDefs.smoothPhaseSlope, `GAIOriginalDefs.smoothPhaseRatio, `GAIOriginalDefs.actualMomentTerm, `GAIOriginalDefs.actualMomentSequence, `GAIOriginalDefs.actualMoment, `GAIOriginalDefs.tailPower, `GAIOriginalDefs.tailCoefficient, `GAIOriginalDefs.tailWeightConstant, `GAIOriginalDefs.tailMajorant, `GAIOriginalDefs.tailExponent, `GAIOriginalDefs.momentBoundConstant, `GAIOriginalDefs.actualWeightedSequence, `GAIOriginalDefs.weightedCoefficientHeight, `GAIOriginalDefs.analyticPrefactor, `GAIOriginalDefs.uniformError].contains m.getPrefix && m.getString!.startsWith "_proof_" then
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
    unless valueDefEq && normalizedDefEq && normalizedEqual do throwError "Full definition kernel/structural mismatch {actual}"

run_cmd liftTermElabM do
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.numerator ``GAIOriginalDefs.numerator true
  afRecord "definition_rfl" ``original_value_numerator
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.poleProduct ``GAIOriginalDefs.poleProduct true
  afRecord "definition_rfl" ``original_value_poleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.actualR ``GAIOriginalDefs.actualR true
  afRecord "definition_rfl" ``original_value_actualR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct ``GAIOriginalDefs.clearedPoleProduct true
  afRecord "definition_rfl" ``original_value_clearedPoleProduct
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedR ``GAIOriginalDefs.clearedR true
  afRecord "definition_rfl" ``original_value_clearedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient ``GAIOriginalDefs.leadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_leadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedR ``GAIOriginalDefs.weightedR true
  afRecord "definition_rfl" ``original_value_weightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.clearedWeightedR ``GAIOriginalDefs.clearedWeightedR true
  afRecord "definition_rfl" ``original_value_clearedWeightedR
  afCompare "definition_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient ``GAIOriginalDefs.weightedLeadingPoleCoefficient true
  afRecord "definition_rfl" ``original_value_weightedLeadingPoleCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phase ``GAIOriginalDefs.phase true
  afRecord "definition_rfl" ``original_value_phase
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseRatio ``GAIOriginalDefs.phaseRatio true
  afRecord "definition_rfl" ``original_value_phaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.phaseSlope ``GAIOriginalDefs.phaseSlope true
  afRecord "definition_rfl" ``original_value_phaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant ``GAIOriginalDefs.upperSlopeConstant true
  afRecord "definition_rfl" ``original_value_upperSlopeConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap ``GAIOriginalDefs.smoothPhaseGap true
  afRecord "definition_rfl" ``original_value_smoothPhaseGap
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope ``GAIOriginalDefs.smoothPhaseSlope true
  afRecord "definition_rfl" ``original_value_smoothPhaseSlope
  afCompare "definition_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio ``GAIOriginalDefs.smoothPhaseRatio true
  afRecord "definition_rfl" ``original_value_smoothPhaseRatio
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm ``GAIOriginalDefs.actualMomentTerm true
  afRecord "definition_rfl" ``original_value_actualMomentTerm
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence ``GAIOriginalDefs.actualMomentSequence true
  afRecord "definition_rfl" ``original_value_actualMomentSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment ``GAIOriginalDefs.actualMoment true
  afRecord "definition_rfl" ``original_value_actualMoment
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailPower ``GAIOriginalDefs.tailPower true
  afRecord "definition_rfl" ``original_value_tailPower
  afCompare "definition_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient ``GAIOriginalDefs.tailCoefficient true
  afRecord "definition_rfl" ``original_value_tailCoefficient
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant ``GAIOriginalDefs.tailWeightConstant true
  afRecord "definition_rfl" ``original_value_tailWeightConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant ``GAIOriginalDefs.tailMajorant true
  afRecord "definition_rfl" ``original_value_tailMajorant
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.tailExponent ``GAIOriginalDefs.tailExponent true
  afRecord "definition_rfl" ``original_value_tailExponent
  afCompare "definition_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant ``GAIOriginalDefs.momentBoundConstant true
  afRecord "definition_rfl" ``original_value_momentBoundConstant
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence ``GAIOriginalDefs.actualWeightedSequence true
  afRecord "definition_rfl" ``original_value_actualWeightedSequence
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight ``GAIOriginalDefs.weightedCoefficientHeight true
  afRecord "definition_rfl" ``original_value_weightedCoefficientHeight
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor ``GAIOriginalDefs.analyticPrefactor true
  afRecord "definition_rfl" ``original_value_analyticPrefactor
  afCompare "definition_compare" ``ZetaNine.AnalyticWeightedBound.uniformError ``GAIOriginalDefs.uniformError true
  afRecord "definition_rfl" ``original_value_uniformError
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.poleProduct_factor ``GAIExpected.poleProduct_factor false
  afRecord "expected_theorem_value" ``GAIExpected.poleProduct_factor
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.poleProduct_ne_zero ``GAIExpected.poleProduct_ne_zero false
  afRecord "expected_theorem_value" ``GAIExpected.poleProduct_ne_zero
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct_ne_zero ``GAIExpected.clearedPoleProduct_ne_zero false
  afRecord "expected_theorem_value" ``GAIExpected.clearedPoleProduct_ne_zero
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.clear_highest_pole ``GAIExpected.clear_highest_pole false
  afRecord "expected_theorem_value" ``GAIExpected.clear_highest_pole
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.clear_weighted_highest_pole ``GAIExpected.clear_weighted_highest_pole false
  afRecord "expected_theorem_value" ``GAIExpected.clear_weighted_highest_pole
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.rising_product ``GAIExpected.rising_product false
  afRecord "expected_theorem_value" ``GAIExpected.rising_product
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.falling_product ``GAIExpected.falling_product false
  afRecord "expected_theorem_value" ``GAIExpected.falling_product
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.clearedPoleProduct_eval ``GAIExpected.clearedPoleProduct_eval false
  afRecord "expected_theorem_value" ``GAIExpected.clearedPoleProduct_eval
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.numerator_eval ``GAIExpected.numerator_eval false
  afRecord "expected_theorem_value" ``GAIExpected.numerator_eval
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_eq ``GAIExpected.leadingPoleCoefficient_eq false
  afRecord "expected_theorem_value" ``GAIExpected.leadingPoleCoefficient_eq
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_eq_even ``GAIExpected.leadingPoleCoefficient_eq_even false
  afRecord "expected_theorem_value" ``GAIExpected.leadingPoleCoefficient_eq_even
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_ne_zero ``GAIExpected.leadingPoleCoefficient_ne_zero false
  afRecord "expected_theorem_value" ``GAIExpected.leadingPoleCoefficient_ne_zero
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.leadingPoleCoefficient_is_integer ``GAIExpected.leadingPoleCoefficient_is_integer false
  afRecord "expected_theorem_value" ``GAIExpected.leadingPoleCoefficient_is_integer
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.signed_leadingPoleCoefficient_pos_even ``GAIExpected.signed_leadingPoleCoefficient_pos_even false
  afRecord "expected_theorem_value" ``GAIExpected.signed_leadingPoleCoefficient_pos_even
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.local_coordinate_identity ``GAIExpected.local_coordinate_identity false
  afRecord "expected_theorem_value" ``GAIExpected.local_coordinate_identity
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.clearedWeightedR_local_coordinate ``GAIExpected.clearedWeightedR_local_coordinate false
  afRecord "expected_theorem_value" ``GAIExpected.clearedWeightedR_local_coordinate
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq ``GAIExpected.weightedLeadingPoleCoefficient_eq false
  afRecord "expected_theorem_value" ``GAIExpected.weightedLeadingPoleCoefficient_eq
  afCompare "theorem_compare" ``ZetaNine.CoefficientMap.weightedLeadingPoleCoefficient_eq_even ``GAIExpected.weightedLeadingPoleCoefficient_eq_even false
  afRecord "expected_theorem_value" ``GAIExpected.weightedLeadingPoleCoefficient_eq_even
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.real_factorial_pos ``GAIExpected.real_factorial_pos false
  afRecord "expected_theorem_value" ``GAIExpected.real_factorial_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_succ ``GAIExpected.log_factorial_succ false
  afRecord "expected_theorem_value" ``GAIExpected.log_factorial_succ
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_upper ``GAIExpected.log_successor_increment_upper false
  afRecord "expected_theorem_value" ``GAIExpected.log_successor_increment_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_successor_increment_lower ``GAIExpected.log_successor_increment_lower false
  afRecord "expected_theorem_value" ``GAIExpected.log_successor_increment_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_lower ``GAIExpected.log_factorial_lower false
  afRecord "expected_theorem_value" ``GAIExpected.log_factorial_lower
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_upper ``GAIExpected.log_factorial_upper false
  afRecord "expected_theorem_value" ``GAIExpected.log_factorial_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticFactorialBounds.log_factorial_pred ``GAIExpected.log_factorial_pred false
  afRecord "expected_theorem_value" ``GAIExpected.log_factorial_pred
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.rational_factorial_ne_zero ``GAIExpected.rational_factorial_ne_zero false
  afRecord "expected_theorem_value" ``GAIExpected.rational_factorial_ne_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.ascending_product_factorial ``GAIExpected.ascending_product_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.ascending_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_falling_product_factorial ``GAIExpected.actual_falling_product_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.actual_falling_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_rising_product_factorial ``GAIExpected.actual_rising_product_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.actual_rising_product_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actual_poleProduct_factorial ``GAIExpected.actual_poleProduct_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.actual_poleProduct_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial ``GAIExpected.actualR_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_factorial_real ``GAIExpected.actualR_factorial_real false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_factorial_real
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_pos ``GAIExpected.actualR_pos false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_real_pos ``GAIExpected.actualR_real_pos false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_real_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalFactorial.actualR_log_factorial ``GAIExpected.actualR_log_factorial false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_log_factorial
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseGap_identity ``GAIExpected.phaseGap_identity false
  afRecord "expected_theorem_value" ``GAIExpected.phaseGap_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseGap_pos ``GAIExpected.phaseGap_pos false
  afRecord "expected_theorem_value" ``GAIExpected.phaseGap_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_pos ``GAIExpected.phaseRatio_pos false
  afRecord "expected_theorem_value" ``GAIExpected.phaseRatio_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_lt_one ``GAIExpected.phaseRatio_lt_one false
  afRecord "expected_theorem_value" ``GAIExpected.phaseRatio_lt_one
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_eq_log_ratio ``GAIExpected.phaseSlope_eq_log_ratio false
  afRecord "expected_theorem_value" ``GAIExpected.phaseSlope_eq_log_ratio
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_neg_right ``GAIExpected.phaseSlope_neg_right false
  afRecord "expected_theorem_value" ``GAIExpected.phaseSlope_neg_right
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.hasDerivAt_mul_log_shift ``GAIExpected.hasDerivAt_mul_log_shift false
  afRecord "expected_theorem_value" ``GAIExpected.hasDerivAt_mul_log_shift
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_hasDerivAt ``GAIExpected.phase_hasDerivAt false
  afRecord "expected_theorem_value" ``GAIExpected.phase_hasDerivAt
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.deriv_phase ``GAIExpected.deriv_phase false
  afRecord "expected_theorem_value" ``GAIExpected.deriv_phase
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_strictAntiOn_right ``GAIExpected.phase_strictAntiOn_right false
  afRecord "expected_theorem_value" ``GAIExpected.phase_strictAntiOn_right
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_le_right_endpoint ``GAIExpected.phase_le_right_endpoint false
  afRecord "expected_theorem_value" ``GAIExpected.phase_le_right_endpoint
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_pos ``GAIExpected.upperSlopeConstant_pos false
  afRecord "expected_theorem_value" ``GAIExpected.upperSlopeConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_eq ``GAIExpected.upperSlopeConstant_eq false
  afRecord "expected_theorem_value" ``GAIExpected.upperSlopeConstant_eq
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseRatio_small_interval_le ``GAIExpected.phaseRatio_small_interval_le false
  afRecord "expected_theorem_value" ``GAIExpected.phaseRatio_small_interval_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phaseSlope_small_interval_le ``GAIExpected.phaseSlope_small_interval_le false
  afRecord "expected_theorem_value" ``GAIExpected.phaseSlope_small_interval_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_one_eq ``GAIExpected.phase_one_eq false
  afRecord "expected_theorem_value" ``GAIExpected.phase_one_eq
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_one ``GAIExpected.smoothPhaseGap_one false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseGap_one
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_hasDerivAt ``GAIExpected.smoothPhaseGap_hasDerivAt false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseGap_hasDerivAt
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_pos ``GAIExpected.smoothPhaseRatio_pos false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseRatio_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseRatio_le_upperSlopeConstant ``GAIExpected.smoothPhaseRatio_le_upperSlopeConstant false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseRatio_le_upperSlopeConstant
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_eq_log_ratio ``GAIExpected.smoothPhaseSlope_eq_log_ratio false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseSlope_eq_log_ratio
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseSlope_nonpos ``GAIExpected.smoothPhaseSlope_nonpos false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseSlope_nonpos
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_antitoneOn ``GAIExpected.smoothPhaseGap_antitoneOn false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseGap_antitoneOn
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.smoothPhaseGap_le_zero ``GAIExpected.smoothPhaseGap_le_zero false
  afRecord "expected_theorem_value" ``GAIExpected.smoothPhaseGap_le_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.mul_one_add_log_div_le ``GAIExpected.mul_one_add_log_div_le false
  afRecord "expected_theorem_value" ``GAIExpected.mul_one_add_log_div_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_identity ``GAIExpected.phase_small_interval_identity false
  afRecord "expected_theorem_value" ``GAIExpected.phase_small_interval_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_small_interval_le_one_add_constant ``GAIExpected.phase_small_interval_le_one_add_constant false
  afRecord "expected_theorem_value" ``GAIExpected.phase_small_interval_le_one_add_constant
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_le_one_add_constant ``GAIExpected.phase_global_le_one_add_constant false
  afRecord "expected_theorem_value" ``GAIExpected.phase_global_le_one_add_constant
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.log_two_lower_rational ``GAIExpected.log_two_lower_rational false
  afRecord "expected_theorem_value" ``GAIExpected.log_two_lower_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.log_three_upper_rational ``GAIExpected.log_three_upper_rational false
  afRecord "expected_theorem_value" ``GAIExpected.log_three_upper_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.upperSlopeConstant_lt_rational ``GAIExpected.upperSlopeConstant_lt_rational false
  afRecord "expected_theorem_value" ``GAIExpected.upperSlopeConstant_lt_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_one_add_constant_lt_certified ``GAIExpected.phase_one_add_constant_lt_certified false
  afRecord "expected_theorem_value" ``GAIExpected.phase_one_add_constant_lt_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_lt_certified ``GAIExpected.phase_global_lt_certified false
  afRecord "expected_theorem_value" ``GAIExpected.phase_global_lt_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticPhase.phase_global_upper_bound ``GAIExpected.phase_global_upper_bound false
  afRecord "expected_theorem_value" ``GAIExpected.phase_global_upper_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.scaled_phase_identity ``GAIExpected.scaled_phase_identity false
  afRecord "expected_theorem_value" ``GAIExpected.scaled_phase_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_phase ``GAIExpected.actualR_log_le_phase false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_log_le_phase
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_log_le_certified ``GAIExpected.actualR_log_le_certified false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_log_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_le_certified ``GAIExpected.actualR_le_certified false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_le_certified
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalLogBound.actualR_compact_bound ``GAIExpected.actualR_compact_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_compact_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_falling_product_le ``GAIExpected.actual_falling_product_le false
  afRecord "expected_theorem_value" ``GAIExpected.actual_falling_product_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_rising_product_tail_le ``GAIExpected.actual_rising_product_tail_le false
  afRecord "expected_theorem_value" ``GAIExpected.actual_rising_product_tail_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_poleProduct_ge ``GAIExpected.actual_poleProduct_ge false
  afRecord "expected_theorem_value" ``GAIExpected.actual_poleProduct_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound_rational ``GAIExpected.actualR_tail_bound_rational false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_tail_bound_rational
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actualR_tail_bound ``GAIExpected.actualR_tail_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticRationalTail.actual_tail_weight_le ``GAIExpected.actual_tail_weight_le false
  afRecord "expected_theorem_value" ``GAIExpected.actual_tail_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.nat_negative_rpow_eq_reciprocal_pow ``GAIExpected.nat_negative_rpow_eq_reciprocal_pow false
  afRecord "expected_theorem_value" ``GAIExpected.nat_negative_rpow_eq_reciprocal_pow
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_summable ``GAIExpected.reciprocal_power_tail_summable false
  afRecord "expected_theorem_value" ``GAIExpected.reciprocal_power_tail_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound ``GAIExpected.reciprocal_power_tail_bound false
  afRecord "expected_theorem_value" ``GAIExpected.reciprocal_power_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticPSeriesTail.reciprocal_power_tail_bound_factored ``GAIExpected.reciprocal_power_tail_bound_factored false
  afRecord "expected_theorem_value" ``GAIExpected.reciprocal_power_tail_bound_factored
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualR_zero_of_pos_le ``GAIExpected.actualR_zero_of_pos_le false
  afRecord "expected_theorem_value" ``GAIExpected.actualR_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_zero_of_pos_le ``GAIExpected.actualMomentTerm_zero_of_pos_le false
  afRecord "expected_theorem_value" ``GAIExpected.actualMomentTerm_zero_of_pos_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentTerm_nonneg ``GAIExpected.actualMomentTerm_nonneg false
  afRecord "expected_theorem_value" ``GAIExpected.actualMomentTerm_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_nonneg ``GAIExpected.actualMomentSequence_nonneg false
  afRecord "expected_theorem_value" ``GAIExpected.actualMomentSequence_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_weight_le ``GAIExpected.actual_compact_weight_le false
  afRecord "expected_theorem_value" ``GAIExpected.actual_compact_weight_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_momentTerm_bound ``GAIExpected.actual_compact_momentTerm_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actual_compact_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailPower_ge ``GAIExpected.tailPower_ge false
  afRecord "expected_theorem_value" ``GAIExpected.tailPower_ge
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.tailCoefficient_nonneg ``GAIExpected.tailCoefficient_nonneg false
  afRecord "expected_theorem_value" ``GAIExpected.tailCoefficient_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_momentTerm_bound ``GAIExpected.actual_tail_momentTerm_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actual_tail_momentTerm_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_summable ``GAIExpected.actualMomentSequence_summable false
  afRecord "expected_theorem_value" ``GAIExpected.actualMomentSequence_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMomentSequence_norm_summable ``GAIExpected.actualMomentSequence_norm_summable false
  afRecord "expected_theorem_value" ``GAIExpected.actualMomentSequence_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_compact_moment_sum_bound ``GAIExpected.actual_compact_moment_sum_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actual_compact_moment_sum_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actual_tail_moment_sum_factorial_bound ``GAIExpected.actual_tail_moment_sum_factorial_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actual_tail_moment_sum_factorial_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_eq_compact_add_tail ``GAIExpected.actualMoment_eq_compact_add_tail false
  afRecord "expected_theorem_value" ``GAIExpected.actualMoment_eq_compact_add_tail
  afCompare "theorem_compare" ``ZetaNine.AnalyticMomentBounds.actualMoment_compact_add_factorial_tail_bound ``GAIExpected.actualMoment_compact_add_factorial_tail_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actualMoment_compact_add_factorial_tail_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_pos ``GAIExpected.tailWeightConstant_pos false
  afRecord "expected_theorem_value" ``GAIExpected.tailWeightConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailWeightConstant_le ``GAIExpected.tailWeightConstant_le false
  afRecord "expected_theorem_value" ``GAIExpected.tailWeightConstant_le
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_pos ``GAIExpected.tailMajorant_pos false
  afRecord "expected_theorem_value" ``GAIExpected.tailMajorant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailWeightConstant ``GAIExpected.log_tailWeightConstant false
  afRecord "expected_theorem_value" ``GAIExpected.log_tailWeightConstant
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_identity ``GAIExpected.log_tailMajorant_identity false
  afRecord "expected_theorem_value" ``GAIExpected.log_tailMajorant_identity
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.log_tailMajorant_upper ``GAIExpected.log_tailMajorant_upper false
  afRecord "expected_theorem_value" ``GAIExpected.log_tailMajorant_upper
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.certified_tailExponent_gap ``GAIExpected.certified_tailExponent_gap false
  afRecord "expected_theorem_value" ``GAIExpected.certified_tailExponent_gap
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.tailMajorant_certified_bound ``GAIExpected.tailMajorant_certified_bound false
  afRecord "expected_theorem_value" ``GAIExpected.tailMajorant_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actual_tail_moment_sum_certified_bound ``GAIExpected.actual_tail_moment_sum_certified_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actual_tail_moment_sum_certified_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.momentBoundConstant_pos ``GAIExpected.momentBoundConstant_pos false
  afRecord "expected_theorem_value" ``GAIExpected.momentBoundConstant_pos
  afCompare "theorem_compare" ``ZetaNine.AnalyticUniformMomentBound.actualMoment_uniform_bound ``GAIExpected.actualMoment_uniform_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actualMoment_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeightedSequence_eq_actual_moment_sum ``GAIExpected.actualWeightedSequence_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeightedSequence_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_hasSum_actual_moments ``GAIExpected.actualWeighted_hasSum_actual_moments false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeighted_hasSum_actual_moments
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_summable ``GAIExpected.actualWeighted_summable false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeighted_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_norm_summable ``GAIExpected.actualWeighted_norm_summable false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeighted_norm_summable
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_tsum_eq_actual_moment_sum ``GAIExpected.actualWeighted_tsum_eq_actual_moment_sum false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeighted_tsum_eq_actual_moment_sum
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualMoment_nonneg ``GAIExpected.actualMoment_nonneg false
  afRecord "expected_theorem_value" ``GAIExpected.actualMoment_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.weightedCoefficientHeight_nonneg ``GAIExpected.weightedCoefficientHeight_nonneg false
  afRecord "expected_theorem_value" ``GAIExpected.weightedCoefficientHeight_nonneg
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actualWeighted_uniform_bound ``GAIExpected.actualWeighted_uniform_bound false
  afRecord "expected_theorem_value" ``GAIExpected.actualWeighted_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.changing_quartics_uniform_bound ``GAIExpected.changing_quartics_uniform_bound false
  afRecord "expected_theorem_value" ``GAIExpected.changing_quartics_uniform_bound
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.uniformError_tendsto_zero ``GAIExpected.uniformError_tendsto_zero false
  afRecord "expected_theorem_value" ``GAIExpected.uniformError_tendsto_zero
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.analyticPrefactor_eq_uniform_exponent ``GAIExpected.analyticPrefactor_eq_uniform_exponent false
  afRecord "expected_theorem_value" ``GAIExpected.analyticPrefactor_eq_uniform_exponent
  afCompare "theorem_compare" ``ZetaNine.AnalyticWeightedBound.actual_weighted_uniform_o_one ``GAIExpected.actual_weighted_uniform_o_one false
  afRecord "expected_theorem_value" ``GAIExpected.actual_weighted_uniform_o_one
  afCompare "selected_wrapper_compare" ``solution ``GAIExpected.changing_quartics_uniform_bound false
  afRecord "selected_wrapper_proof" ``solution
