import Definitions.Def_APSP299791_Defs5
import Theorems.Thm_ThreeSumSharpTail_pruned_offline_steps

namespace ThreeSumSharpTail

theorem detection_cost_from_native_count
    (G : Light.Sec4.RatParams) (a s : ℚ) (ha0 : 0 < a)
    (A B k : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hcost : ∀ N D : ℕ, 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
      Light.Sec4.CostsWithinP G C N D
        ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ))
        ((D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)))
    (heq : ∀ N D : ℕ, 1 ≤ N → 1 ≤ D →
      ((D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) ↔ D ^ B ≤ N ^ A))
    (P : Light.Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Light.Need)
    (hneed : Light.PolyNeedN need) (hsol : Light.SolvesN Light.lopCountTask P p Tn need)
    (htime : ∀ N D w : ℕ, Tn [N, D, w] = k +
      if D ^ B ≤ N ^ A then Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w
      else 40 * ((w + 1) * (D + 1)))
    (hdetect : ThreeSumApsp.Claim.LopDetectFromCount Light.lightModel) :
    ∃ (K : ℝ) (Td : ℕ → ℕ → ℕ → ℝ), 0 ≤ K ∧ Light.lightModel.lopDetect Td ∧
      ∀ N D w : ℕ, 1 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ (a : ℝ) →
        Td N D w ≤ K * ((N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ) +
          (w : ℝ) * (D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1) +
          (N : ℝ) * D + w + 1) := by
  let pre (N D : ℕ) : ℝ := (N : ℝ) ^ 2 * (Real.log D + 1) ^ 2 / (D : ℝ) ^ (s : ℝ)
  let query (D : ℕ) : ℝ := (D : ℝ) ^ (1 / 2 - (s : ℝ)) * (Real.log D + 1)
  have hpre0 (N D : ℕ) : 0 ≤ pre N D := by dsimp [pre]; positivity
  have hquery0 (D : ℕ) (hD : 1 ≤ D) : 0 ≤ query D := by
    dsimp [query]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ D by exact_mod_cast hD)])
  obtain ⟨L, hL⟩ := ThreeSumSharpTail.pruned_offline_steps G C hC Light.Sec4.cShared30 k
  let c : ℝ := max 0 L
  have hc : 0 ≤ c := le_max_left _ _
  let Tc (N D w : ℕ) : ℝ := if D ^ B ≤ N ^ A then c * (pre N D + (w : ℝ) * query D)
    else (k : ℝ) + 40 * (((w : ℝ) + 1) * ((D : ℝ) + 1))
  have hcount : Light.lightModel.lopCount Tc := by
    refine ⟨P, p, Tn, need, hneed, hsol, fun N D w w' hN hD hww => ?_⟩
    rw [htime N D w]
    dsimp [Tc]
    by_cases hr : D ^ B ≤ N ^ A
    · rw [if_pos hr, if_pos hr]
      have hh := hL N D (pre N D) (query D) w (hcost N D hD ((heq N D hN hD).mpr hr))
      have hbase : 0 ≤ pre N D + (w : ℝ) * query D :=
        add_nonneg (hpre0 N D) (mul_nonneg (by positivity) (hquery0 D hD))
      have hwwR : (w : ℝ) ≤ (w' : ℝ) := by exact_mod_cast hww
      have hmono : pre N D + (w : ℝ) * query D ≤ pre N D + (w' : ℝ) * query D := by
        simpa only [add_comm] using
          add_le_add_left (mul_le_mul_of_nonneg_right hwwR (hquery0 D hD)) (pre N D)
      have hh0 : (k : ℝ) + (Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w : ℝ) ≤
          L * (pre N D + (w : ℝ) * query D) := by simpa only [add_comm] using hh
      have hh' : (k : ℝ) + (Light.Sec4.tOffline32P Light.Sec4.cShared30 G N D w : ℝ) ≤
          c * (pre N D + (w' : ℝ) * query D) :=
        hh0.trans
          ((mul_le_mul_of_nonneg_right (le_max_right 0 L) hbase).trans
            (mul_le_mul_of_nonneg_left hmono hc))
      simpa only [Nat.cast_add] using hh'
    · rw [if_neg hr, if_neg hr]
      push_cast
      gcongr
  obtain ⟨J, hJ⟩ := hdetect
  refine ⟨c + max 0 J, fun N D w => Tc N D w + J * ((w : ℝ) + 1),
    add_nonneg hc (le_max_left _ _), hJ Tc hcount, fun N D w hD hr => ?_⟩
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
  have hN : 1 ≤ N := by
    by_contra hN
    have hN0 : N = 0 := by omega
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    simp only [hN0, Nat.cast_zero, Real.zero_rpow (ne_of_gt haR)] at hr
    linarith
  have hnat : D ^ B ≤ N ^ A := (heq N D hN hD).mp hr
  change Tc N D w + J * ((w : ℝ) + 1) ≤ _
  dsimp [Tc]
  rw [if_pos hnat]
  have hb0 : 0 ≤ pre N D + (w : ℝ) * query D :=
    add_nonneg (hpre0 N D) (mul_nonneg (by positivity) (hquery0 D hD))
  have ho0 : 0 ≤ (N : ℝ) * D + w + 1 := by positivity
  have hw1 : (w : ℝ) + 1 ≤ (N : ℝ) * D + w + 1 := by
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (Nat.cast_nonneg D : (0 : ℝ) ≤ D)]
  have hj0 : 0 ≤ max 0 J := le_max_left _ _
  have hover : J * ((w : ℝ) + 1) ≤ max 0 J * ((N : ℝ) * D + w + 1) :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hw1 hj0)
  have hfinal : c * (pre N D + (w : ℝ) * query D) + J * ((w : ℝ) + 1) ≤
      (c + max 0 J) * (pre N D + (w : ℝ) * query D + (N : ℝ) * D + w + 1) := by
    nlinarith [mul_nonneg hc ho0, mul_nonneg hj0 hb0]
  simpa only [pre, query, mul_assoc] using hfinal

end ThreeSumSharpTail

#print axioms ThreeSumSharpTail.detection_cost_from_native_count
