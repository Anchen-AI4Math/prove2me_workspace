import Mathlib
import Definitions.Def_ThreeSumSharpTail_Analysis
import Definitions.Def_APSPSource_RemainingDefinitions
import Theorems.Thm_ThreeSumApsp_Spec_length_nineStrs
import Theorems.Thm_ThreeSumSharpTail_sharp_normalized_tail

open scoped BigOperators
open ThreeSumApsp ThreeSumApsp.Spec Finset

namespace ThreeSumSharpTail

theorem raw_tile_lists_le (c m t : ℕ) (hmL : m ≤ c * m) (ht : t ≤ m) :
    ((List.range (m - t + 1)).map fun e => (starBoxes (c * m) m t e).length).sum ≤
      (m + 1) * ∑ d ∈ Finset.Icc t m, boxCount c m d := by
  have hreflect : ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) =
      ∑ d ∈ Finset.Icc t m, boxCount c m d := by
    calc
      _ = ∑ f ∈ Finset.range (m - t + 1), boxCount c m (m - f) := by
        apply Finset.sum_congr rfl
        intro f hf
        have hf' : f ≤ m := by have := Finset.mem_range.mp hf; omega
        unfold boxCount
        rw [Nat.sub_sub_self hf']
        congr 2
        omega
      _ = _ := by
        rw [Finset.range_eq_Ico, Finset.sum_Ico_reflect (boxCount c m) 0 (n := m) (by omega)]
        congr 1
        ext d
        simp only [Finset.mem_Ico, Finset.mem_Icc]
        omega
  have hterm (e : ℕ) : (starBoxes (c * m) m t e).length ≤
      ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) := by
    rw [starBoxes, List.length_map, length_nineStrs]
    exact Finset.sum_le_sum_of_subset (by
      intro f hf
      exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hf).2; omega))
  calc
    _ ≤ ((List.range (m - t + 1)).map fun _ =>
          ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f)).sum :=
      List.sum_le_sum (fun e _ => hterm e)
    _ = (m - t + 1) * ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) := by
      simp
    _ ≤ (m + 1) * ∑ f ∈ Finset.range (m - t + 1), (c * m).choose f * 9 ^ (c * m - f) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by rw [hreflect]

theorem raw_tile_lists_sharp (c m : ℕ) (hc : 10 < c) (hm : 1 ≤ m)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ9 : θ < 9 / 10) :
    (((List.range (m - ⌈θ * (m : ℝ)⌉₊ + 1)).map fun e =>
        (starBoxes (c * m) m ⌈θ * (m : ℝ)⌉₊ e).length).sum : ℝ) ≤
      ((m : ℝ) + 1) * (boxCount c m 0 : ℝ) *
        (((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
          Real.rpow ((4 : ℝ) ^ m) (-sharpSaving c θ)) := by
  have hmL : m ≤ c * m := Nat.le_mul_of_pos_left _ (by omega)
  have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have ht : ⌈θ * (m : ℝ)⌉₊ ≤ m := Nat.ceil_le.mpr (by nlinarith)
  have hM : (0 : ℝ) < boxCount c m 0 := by
    exact_mod_cast (show 0 < boxCount c m 0 from by
      simp only [boxCount, Nat.sub_zero, Nat.add_zero]
      exact Nat.mul_pos (Nat.choose_pos hmL) (by positivity))
  have hcount := raw_tile_lists_le c m ⌈θ * (m : ℝ)⌉₊ hmL ht
  have hcountR :
      (((List.range (m - ⌈θ * (m : ℝ)⌉₊ + 1)).map fun e =>
        (starBoxes (c * m) m ⌈θ * (m : ℝ)⌉₊ e).length).sum : ℝ) ≤
        ((m : ℝ) + 1) *
          ((∑ d ∈ Finset.Icc ⌈θ * (m : ℝ)⌉₊ m, boxCount c m d : ℕ) : ℝ) := by
    exact_mod_cast hcount
  have htail := sharp_normalized_tail c m hc hm θ hθ0 hθ9
  rw [div_le_iff₀ hM] at htail
  calc
    _ ≤ ((m : ℝ) + 1) *
        ((∑ d ∈ Finset.Icc ⌈θ * (m : ℝ)⌉₊ m, boxCount c m d : ℕ) : ℝ) := hcountR
    _ ≤ ((m : ℝ) + 1) *
        ((((c : ℝ) * m + 1) / (1 - 9 / ((c : ℝ) - 1)) *
          Real.rpow ((4 : ℝ) ^ m) (-sharpSaving c θ)) * (boxCount c m 0 : ℝ)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

end ThreeSumSharpTail
