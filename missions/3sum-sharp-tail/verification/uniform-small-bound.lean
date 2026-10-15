import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Theorem19
import Definitions.Def_APSP299791_Defs5

namespace ThreeSumApsp.Theorem19FullDUniformize

theorem small_uniform_bound (δ K₀ : ℝ) (e N : ℕ) (p : SizeBound)
    (hδ0 : 0 ≤ δ) (hK : 1 ≤ K₀)
    (hsmall : (1 ≤ p.s ∧ 1 ≤ p.u) ∧ p.s < N) :
    K₀ * uniformShape (7 / 4000) 1 p ≤
      (K₀ * (N : ℝ) ^ δ * (Real.log N + 1)) * uniformShape δ e p := by
  have hs : (1 : ℝ) ≤ p.s := by exact_mod_cast hsmall.1.1
  have hspos : 0 < (p.s : ℝ) := by linarith
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : 0 < (N : ℝ) := by linarith
  have hsN : (p.s : ℝ) ≤ N := by exact_mod_cast hsmall.2.le
  have hlog0 : 0 ≤ Real.log p.s := Real.log_nonneg hs
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlog : Real.log p.s + 1 ≤ Real.log N + 1 := by
    simpa only [add_comm] using add_le_add_right (Real.log_le_log hspos hsN) 1
  have hloge : 1 ≤ (Real.log p.s + 1) ^ e := one_le_pow₀ (by linarith)
  have hlogfactor : Real.log p.s + 1 ≤
      (Real.log N + 1) * (Real.log p.s + 1) ^ e := by
    calc
      _ ≤ Real.log N + 1 := hlog
      _ ≤ (Real.log N + 1) * (Real.log p.s + 1) ^ e :=
        le_mul_of_one_le_right (by linarith) hloge
  have hpow : (p.s : ℝ) ^ (3 - (7 / 4000 : ℝ)) ≤
      (p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ := by
    calc
      _ ≤ (p.s : ℝ) ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hs (by norm_num)
      _ = (p.s : ℝ) ^ (3 - δ) * (p.s : ℝ) ^ δ := by
        rw [← Real.rpow_add hspos]
        congr 1
        ring
      _ ≤ (p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ := by
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hspos.le hsN hδ0)
          (Real.rpow_nonneg hspos.le _)
  have hbase : (p.s : ℝ) ^ (3 - (7 / 4000 : ℝ)) * (Real.log p.s + 1) ≤
      ((p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ) *
        ((Real.log N + 1) * (Real.log p.s + 1) ^ e) := by
    exact mul_le_mul hpow hlogfactor (by linarith) (by positivity)
  have hweight : 0 ≤ (1 + logU p.u) ^ 2 := sq_nonneg _
  have hK0 : 0 ≤ K₀ := by linarith
  unfold uniformShape
  simp only [pow_one]
  calc
    _ ≤ K₀ * ((((p.s : ℝ) ^ (3 - δ) * (N : ℝ) ^ δ) *
      ((Real.log N + 1) * (Real.log p.s + 1) ^ e)) * (1 + logU p.u) ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbase hweight) hK0
    _ = _ := by ring

theorem large_uniform_bound (δ K : ℝ) (e n₀ : ℕ) (T : ℕ → ℝ → ℝ)
    (hb : ∀ (n : ℕ) (κ u : ℝ), n₀ ≤ n → 1 ≤ κ → u ≤ (n : ℝ) ^ κ →
      T n u ≤ K * (κ * ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)))
    (n : ℕ) (u : ℝ) (hn : n₀ ≤ n) (h3 : 3 ≤ n) (hu : 1 ≤ u) :
    T n u ≤ max 1 K * uniformShape δ e ⟨n, u⟩ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 1 ≤ Real.log n := Real.one_le_log_natCast_of_three_le h3
  have hup : 0 < u := by linarith
  have hword0 : 0 ≤ logU u := by
    unfold logU
    apply Real.log_nonneg
    exact le_trans (by norm_num) (le_max_right u 2)
  have hword1 : 1 ≤ 1 + logU u := by linarith
  have hulog : Real.log u ≤ logU u :=
    Real.log_le_log hup (le_max_left u 2)
  have hκ : max 1 (Real.log u / Real.log n) ≤ (1 + logU u) ^ 2 := by
    apply le_trans (b := 1 + logU u)
    · apply max_le hword1
      have hdiv : Real.log u / Real.log n ≤ Real.log u :=
        div_le_self (Real.log_nonneg hu) hlogn
      linarith
    · exact le_self_pow₀ hword1 two_ne_zero
  have hweight : u ≤ (n : ℝ) ^ max 1 (Real.log u / Real.log n) := by
    calc
      u = (n : ℝ) ^ (Real.log u / Real.log n) := by
        rw [Real.rpow_def_of_pos hnpos, mul_div_cancel₀ _ (by linarith), Real.exp_log hup]
      _ ≤ (n : ℝ) ^ max 1 (Real.log u / Real.log n) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
  have hbase0 : 0 ≤ max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) := by positivity
  have hbase : max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e) ≤ uniformShape δ e ⟨n, u⟩ := by
    calc
      _ ≤ (1 + logU u) ^ 2 * ((n : ℝ) ^ (3 - δ) * (Real.log n + 1) ^ e) := by
        gcongr
        linarith
      _ = _ := by unfold uniformShape; simp; ring
  calc
    T n u ≤ K * (max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) :=
        hb n _ u hn (le_max_left _ _) hweight
    _ ≤ max 1 K * (max 1 (Real.log u / Real.log n) *
      ((n : ℝ) ^ (3 - δ) * Real.log n ^ e)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hbase0
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

theorem uniformize_of_small_solver (M : DetTimeModel) (δ : ℝ) (e n₀ : ℕ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hex : Claim.Theorem_19_explicitAt M δ e n₀)
    (hold : Claim.ExactTriangleUniform M (7 / 4000) 1)
    (hchoose : Closure.ChooseBySize M) (hmono : Closure.MonoExactTriangle M) :
    Claim.ExactTriangleUniform M δ e := by
  obtain ⟨K, T, hT, hb⟩ := hex
  obtain ⟨K₀, hK₀, hT₀⟩ := hold
  let N : ℕ := max n₀ 3
  obtain ⟨C₀, hch⟩ := hchoose N
  let Csmall : ℝ := K₀ * (N : ℝ) ^ δ * (Real.log N + 1)
  let C : ℝ := 1 + Csmall + max 1 K + max 0 C₀
  have hN1 : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by dsimp [N]; omega)
  have hCs : 0 ≤ Csmall := by
    dsimp [Csmall]
    exact mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _))
      (by linarith [Real.log_nonneg hN1])
  have hCl : 0 ≤ max 1 K := le_trans (by norm_num) (le_max_left _ _)
  have hCo : 0 ≤ max 0 C₀ := le_max_left _ _
  have hC1 : 1 ≤ C := by dsimp [C]; linarith
  refine ⟨C, hC1, hmono _ _ (fun n u hn hu => ?_)
    (hch (uniformTime K₀ (7 / 4000) 1) T hT₀ hT)⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog1 : 1 ≤ Real.log n + 1 := by linarith [Real.log_nonneg hnR]
  have hwords1 : 1 ≤ 1 + logU u := by
    have hlogU : 0 ≤ logU u := Real.log_nonneg (le_trans (by norm_num) (le_max_right u 2))
    linarith
  have hshape1 : 1 ≤ uniformShape δ e ⟨n, u⟩ := by
    unfold uniformShape
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (Real.one_le_rpow hnR (by linarith)) (one_le_pow₀ hlog1))
      (one_le_pow₀ hwords1)
  have hshape0 : 0 ≤ uniformShape δ e ⟨n, u⟩ := by linarith
  have hbranch : (if n < N then uniformTime K₀ (7 / 4000) 1 n u else T n u) ≤
      (Csmall + max 1 K) * uniformShape δ e ⟨n, u⟩ := by
    by_cases hs : n < N
    · rw [if_pos hs]
      have hh := small_uniform_bound δ K₀ e N ⟨n, u⟩ hδ0 hK₀ ⟨⟨hn, hu⟩, hs⟩
      exact hh.trans (mul_le_mul_of_nonneg_right (by dsimp [Csmall]; linarith) hshape0)
    · rw [if_neg hs]
      have hnn₀ : n₀ ≤ n := by dsimp [N] at hs; omega
      have h3 : 3 ≤ n := by dsimp [N] at hs; omega
      exact (large_uniform_bound δ K e n₀ T hb n u hnn₀ h3 hu).trans
        (mul_le_mul_of_nonneg_right (by linarith) hshape0)
  have hcost : C₀ ≤ max 0 C₀ * uniformShape δ e ⟨n, u⟩ :=
    (le_max_right _ _).trans (le_mul_of_one_le_right hCo hshape1)
  change _ ≤ C * uniformShape δ e ⟨n, u⟩
  dsimp [C]
  nlinarith

end ThreeSumApsp.Theorem19FullDUniformize

#print axioms ThreeSumApsp.Theorem19FullDUniformize.small_uniform_bound
#print axioms ThreeSumApsp.Theorem19FullDUniformize.large_uniform_bound
#print axioms ThreeSumApsp.Theorem19FullDUniformize.uniformize_of_small_solver
