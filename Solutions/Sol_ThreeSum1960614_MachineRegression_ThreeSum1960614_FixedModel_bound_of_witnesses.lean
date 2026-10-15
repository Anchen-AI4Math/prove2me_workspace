import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_MachineRegression_Submission_ThreeSum_FixedModelAlgebra
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

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
open _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel

/-- Four necessary charges suffice; the point witnesses remain explicit premises. -/
theorem solution (e b S th terminal ratio R : ℝ)
    (hmodel : _root_.ThreeSum1960614.ModelFeasible 232 e b S th terminal ratio R)
    (hE : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0 ≤ _root_.ThreeSum1960614.E 232) (hk : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0 ≤ _root_.ThreeSum1960614.kappa 232) (hrho : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0 ≤ ratio)
    (hgamma : th ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split → _root_.ThreeSum1960614.gamma 232 th ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap)
    (hentropy : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split ≤ th → _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor ≤ _root_.ThreeSum1960614.entropy th) : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget < R := by
  rcases hmodel with ⟨he,_,hb,hS,_,_,_,_,_,hswitch,_,hcost⟩
  by_cases hR : 2 ≤ R
  · exact lt_of_lt_of_le (by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget]) hR
  let delta : ℝ := 2-R
  have hbox : 2-e*S ≤ R := hcost _ (by simp [_root_.ThreeSum1960614.ledger])
  have henc : 1+e*(_root_.ThreeSum1960614.E 232-b) ≤ R := hcost _ (by simp [_root_.ThreeSum1960614.ledger])
  have hini : 2-e*(1/2+b-_root_.ThreeSum1960614.entropy th) ≤ R := hcost _ (by simp [_root_.ThreeSum1960614.ledger])
  have hrec : 2-e*(1/2-b-_root_.ThreeSum1960614.kappa 232-ratio*(1+S-2*b)) ≤ R :=
    hcost _ (by simp [_root_.ThreeSum1960614.ledger])
  have hEscale := mul_le_mul_of_nonneg_left hE he.le
  have hkscale := mul_le_mul_of_nonneg_left hk he.le
  have hrscale := mul_le_mul_of_nonneg_left hrho
    (mul_nonneg he.le (show 0 ≤ 1+S-2*b by linarith only [hS,hb]))
  have hbs : (1+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*delta+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*(e*b) ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A*e := by
    dsimp [delta,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0]
    dsimp [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0] at hrscale
    nlinarith only [hbox,hrec,hkscale,hrscale]
  have hapos : 0 < _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a := by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0]
  have hswitchScale := mul_le_mul_of_nonneg_left hswitch he.le
  have hsave : delta ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap*e := by
    rcases le_total th _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.split with hleft | hright
    · have hgscale := mul_le_mul_of_nonneg_left (hgamma hleft) he.le
      have hswitchDelta : delta-2*e*b ≤ e*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap := by
        dsimp [delta]
        nlinarith only [hbox,hswitchScale,hgscale]
      have hs := mul_le_mul_of_nonneg_left hswitchDelta hapos.le
      have hcombine : 3*delta ≤ (2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap)*e := by
        dsimp [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0] at hbs hs ⊢
        nlinarith only [hbs,hs]
      have hcap : 2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A+_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap ≤ 3*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap := by
        norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.gammaCap,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap]
      have hcapScale := mul_le_mul_of_nonneg_right hcap he.le
      nlinarith only [hcombine,hcapScale]
    · have hhscale := mul_le_mul_of_nonneg_left (hentropy hright) he.le
      have hinitDelta : delta ≤ e/2+e*b-e*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor := by
        dsimp [delta]
        nlinarith only [hini,hhscale]
      have hs := mul_le_mul_of_nonneg_left hinitDelta hapos.le
      have hcombine : (2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*delta ≤
          (1-2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor)*e := by
        dsimp [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0] at hbs hs ⊢
        nlinarith only [hbs,hs]
      have hcap : 1-2*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor ≤ (2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap := by
        norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.entropyFloor,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap]
      have hcapScale := mul_le_mul_of_nonneg_right hcap he.le
      have hden : 0 < 2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0 := by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0]
      norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0] at hcombine hcapScale ⊢
      nlinarith only [hcombine,hcapScale]
  have henc0 : e*(_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0-b)+delta ≤ 1 := by
    dsimp [delta]
    nlinarith only [henc,hEscale]
  have hsenc := mul_le_mul_of_nonneg_left henc0 hapos.le
  have hbudget : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C*e+(2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*delta ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a := by
    dsimp [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0] at hsenc hbs ⊢
    nlinarith only [hsenc,hbs]
  have hC : 0 < _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C := by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0]
  have hU : 0 < _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap := by norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap]
  have hsaveC := mul_le_mul_of_nonneg_left hsave hC.le
  have hbudgetU := mul_le_mul_of_nonneg_left hbudget hU.le
  have hfinal : (_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C+(2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap)*delta ≤ _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap := by
    nlinarith only [hsaveC,hbudgetU]
  have hstrict : _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap < (_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C+(2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap)*(2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget) := by
    norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget]
  have hden : 0 < _root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C+(2-_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0)*_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap := by
    norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap]
  dsimp [delta] at hfinal
  norm_num [_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.C,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.a,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.A,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.ratio0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.e0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.k0,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.savingCap,_root_.ThreeSum1960614.MachineRegression.ThreeSum1960614.FixedModel.lowerTarget] at hfinal ⊢
  linarith only [hfinal]

#print axioms solution
