import Definitions.Def_ThreeSum1960614_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSum1960614

theorem ThreeSum1960614.high_precision_logs :
    ((6931471805599453094172 / 10 ^ 22 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 6931471805599453094173 / 10 ^ 22) ∧
    ((5947071077466927895143 / 10 ^ 22 : ℝ) ≤ Real.log (29 / 16) ∧
      Real.log (29 / 16) ≤ 5947071077466927895144 / 10 ^ 22) ∧
    ((43196611445164148724 / 10 ^ 22 : ℝ) ≤ Real.log (232 / 231) ∧
      Real.log (232 / 231) ≤ 43196611445164148725 / 10 ^ 22) ∧
    ((21574981400211907723 / 10 ^ 22 : ℝ) ≤ Real.log (464 / 463) ∧
      Real.log (464 / 463) ≤ 21574981400211907724 / 10 ^ 22) ∧
    ((2570554035235070921259 / 10 ^ 22 : ℝ) ≤ Real.log (32 * theta) ∧
      Real.log (32 * theta) ≤ 2570554035235070921260 / 10 ^ 22) ∧
    ((6518981167335747474116 / 10 ^ 22 : ℝ) ≤ Real.log (2 * (1 - theta)) ∧
      Real.log (2 * (1 - theta)) ≤ 6518981167335747474117 / 10 ^ 22)  := by sorry
