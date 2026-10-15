import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_MachineRegression_Submission_ThreeSum_FixedModelAlgebra
import Definitions.Def_ThreeSum1960614_MachineRegression_Submission_ThreeSum_ModelWitnessLogs
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

namespace ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel
end ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel

namespace ThreeSum1960614.MachineRegression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators

noncomputable section
namespace ThreeSum1960614.FixedModel



private def private_9f68576d46_series (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z^(2*i+1)/(2*i+1)

private theorem private_3c576917b2_interval {y z L U : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1+z)/(1-z)=y) (n : ℕ)
    (hl : L ≤ 2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series n z)
    (hu : 2*(_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series n z+z^(2*n+1)/(1-z^2)) ≤ U) :
    L ≤ Real.log y ∧ Real.log y ≤ U := by
  have hleft := mul_le_mul_of_nonneg_left (Real.sum_range_le_log_div hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hright := mul_le_mul_of_nonneg_left (Real.log_div_le_sum_range_add hz0 hz1 n)
    (by norm_num : (0 : ℝ) ≤ 2)
  have hlo : 2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series n z ≤ Real.log y := by
    rw [← hy]
    simpa [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using hleft
  have hhi : Real.log y ≤ 2*(_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series n z+z^(2*n+1)/(1-z^2)) := by
    rw [← hy]
    calc
      _ = 2*(1/2*Real.log ((1+z)/(1-z))) := by ring
      _ ≤ _ := by simpa [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series] using hright
  exact ⟨hl.trans hlo,hhi.trans hu⟩



end ThreeSum1960614.FixedModel

end

end ThreeSum1960614.MachineRegression

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000
open scoped BigOperators
open _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel

theorem solution :
    ((1285276917605861577967/5000000000000000000000 : ℝ) ≤ Real.log (32*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split) ∧
      Real.log (32*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split) ≤ (514110767042344631187/2000000000000000000000 : ℝ)) ∧
    ((6518981175759055705591/10000000000000000000000 : ℝ) ≤ Real.log (2*(1-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split)) ∧
      Real.log (2*(1-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split)) ≤ (814872646969881963199/1250000000000000000000 : ℝ)) ∧
    ((437298312323441179/2500000000000000000000 : ℝ) ≤ Real.log (1+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split/231) ∧
      Real.log (1+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split/231) ≤ (1749193249293764717/10000000000000000000000 : ℝ)) ∧
    ((638270279972769945753/2000000000000000000000 : ℝ) ≤ Real.log (8*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint) ∧
      Real.log (8*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint) ≤ (1595675699931924864383/5000000000000000000000 : ℝ)) ∧
    ((1008829056134582490741/2000000000000000000000 : ℝ) ≤ Real.log (2*(1-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint)) ∧
      Real.log (2*(1-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint)) ≤ (2522072640336456226853/5000000000000000000000 : ℝ)) ∧
    ((58146699145150531/78125000000000000000 : ℝ) ≤ Real.log (1+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint/231) ∧
      Real.log (1+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint/231) ≤ (7442777490579267969/10000000000000000000000 : ℝ)) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (57249363698173/447874363698173 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 18 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (2872438136301827/9122438136301827 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 26 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (84187287899391/962584187287899391 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 4 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (234960785302793/1484960785302793 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 18 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (1640039214697207/6640039214697207 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 24 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])
  · exact _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_3c576917b2_interval (z := (286653595100931/770286653595100931 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratioPoint]) 5 (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series]) (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.private_9f68576d46_series])

#print axioms solution
