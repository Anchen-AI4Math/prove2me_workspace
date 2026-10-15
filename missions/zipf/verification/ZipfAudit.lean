import Definitions.Def_ZipfLaw_Defs
set_option autoImplicit false

namespace ZipfAudit.log_zipfPMF_affine

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

private lemma log_term (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  have hH := zipf_harmonic_pos N (le_trans hk1 hkN) s
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hp := Real.rpow_pos_of_pos hkpos s
  rw [zipfPMF, if_pos ⟨hk1, hkN⟩, Real.log_div (by positivity) hH.ne',
    Real.log_div (by norm_num) hp.ne', Real.log_one, Real.log_rpow hkpos]
  ring

theorem solution (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  exact log_term N s k hk1 hkN

#print axioms solution


example  (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := solution N s k hk1 hkN

end ZipfAudit.log_zipfPMF_affine

namespace ZipfAudit.monkey_typing_power_law

set_option autoImplicit false

open ZipfLaw

private lemma zipf_geometric_count (m n : ℕ) (hm : 2 ≤ m) :
    (∑ j ∈ Finset.range n, m ^ j) ≤ m ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    calc
      _ ≤ m ^ n + m ^ n := Nat.add_le_add_right ih _
      _ ≤ m ^ n * m := by simpa [Nat.mul_two] using Nat.mul_le_mul_left (m ^ n) hm

theorem solution (m : ℕ) (hm : 2 ≤ m) (q : ℝ) (hq : 0 < q) (hmq : (m : ℝ) * q < 1)
    (e : ℕ → List (Fin m)) (he_inj : Function.Injective e)
    (he_range : Set.range e = {w | w ≠ []})
    (he_sorted : Antitone (fun r => monkeyWordProb m q (e r))) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ r : ℕ,
      C₁ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) ≤ monkeyWordProb m q (e r) ∧
        monkeyWordProb m q (e r) ≤ C₂ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) := by
  classical
  have hmreal : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  have hmpos : (0 : ℝ) < m := lt_trans zero_lt_one hmreal
  have hq1 : q < 1 := by nlinarith
  have hS : 0 < 1 - (m : ℝ) * q := by linarith
  have hnonempty (i : ℕ) : e i ≠ [] := by
    have hi : e i ∈ Set.range e := ⟨i, rfl⟩
    rw [he_range] at hi
    exact hi
  refine ⟨q * (1 - m * q), (1 - m * q) / q, by positivity, by positivity, ?_⟩
  intro r
  let L := (e r).length
  have hL : 1 ≤ L := by
    have := hnonempty r
    simpa only [L, List.length_pos_iff, Nat.succ_le_iff] using List.length_pos_iff.mpr this
  have hlength (i : ℕ) (hi : i ≤ r) : (e i).length ≤ L := by
    have hprob := he_sorted hi
    unfold monkeyWordProb at hprob
    have hpow : q ^ L ≤ q ^ (e i).length := (mul_le_mul_iff_left₀ hS).mp hprob
    exact (pow_le_pow_iff_right_of_lt_one₀ hq hq1).mp hpow
  let T := (Finset.range (r + 1)).image e
  have hT : T.card = r + 1 := by
    simp [T, Finset.card_image_of_injective, he_inj]
  have hmap : (T : Set (List (Fin m))).MapsTo List.length (Finset.range (L + 1)) := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨i, hi, rfl⟩
    exact Finset.mem_range.mpr (by have := hlength i (by have := Finset.mem_range.mp hi; omega); omega)
  have hupper : r + 1 ≤ m ^ (L + 1) := by
    calc
      r + 1 = T.card := hT.symm
      _ = ∑ j ∈ Finset.range (L + 1), (T.filter (fun w => w.length = j)).card :=
        Finset.card_eq_sum_card_fiberwise hmap
      _ ≤ ∑ j ∈ Finset.range (L + 1), m ^ j := by
        apply Finset.sum_le_sum
        intro j _
        simpa using (Finset.card_filter_length_eq_le (T := T) (s := j))
      _ ≤ m ^ (L + 1) := zipf_geometric_count m (L + 1) hm
  have hlower : m ^ (L - 1) ≤ r + 1 := by
    by_cases hn : L - 1 = 0
    · simp [hn]
    · let n := L - 1
      have hnpos : 0 < n := by omega
      have hnL : n < L := by omega
      have hex (v : Fin n → Fin m) : ∃ i : ℕ, e i = List.ofFn v := by
        apply Set.mem_range.mp
        rw [he_range]
        intro hnil
        have hlen := congrArg List.length hnil
        simp only [List.length_ofFn, List.length_nil] at hlen
        omega
      let idx (v : Fin n → Fin m) : ℕ := Classical.choose (hex v)
      have heq (v : Fin n → Fin m) : e (idx v) = List.ofFn v := Classical.choose_spec (hex v)
      have hidx (v : Fin n → Fin m) : idx v < r + 1 := by
        by_contra hbad
        have hprob := he_sorted (show r ≤ idx v by omega)
        unfold monkeyWordProb at hprob
        change q ^ (e (idx v)).length * (1 - m * q) ≤ q ^ L * (1 - m * q) at hprob
        rw [heq, List.length_ofFn] at hprob
        have hstrict := mul_lt_mul_of_pos_right (pow_right_strictAnti₀ hq hq1 hnL) hS
        change q ^ n * (1 - m * q) ≤ q ^ L * (1 - m * q) at hprob
        linarith
      let g (v : Fin n → Fin m) : Fin (r + 1) := ⟨idx v, hidx v⟩
      have hg : Function.Injective g := by
        intro v w hvw
        apply List.ofFn_injective
        have hi : idx v = idx w := congrArg Fin.val hvw
        rw [← heq v, ← heq w, hi]
      simpa [n] using Fintype.card_le_of_injective g hg
  have hlower' : m ^ L ≤ m * (r + 1) := by
    calc
      m ^ L = m ^ (L - 1) * m := by rw [← pow_succ, Nat.sub_add_cancel hL]
      _ ≤ (r + 1) * m := Nat.mul_le_mul_right m hlower
      _ = m * (r + 1) := Nat.mul_comm _ _
  have hupper_real : (r : ℝ) + 1 ≤ (m : ℝ) ^ (L + 1) := by exact_mod_cast hupper
  have hlower_real : (m : ℝ) ^ L ≤ (m : ℝ) * ((r : ℝ) + 1) := by exact_mod_cast hlower'
  have hlog : -Real.logb (m : ℝ) (1 / q) = Real.logb (m : ℝ) q := by
    simp [one_div, Real.logb_inv]
  have hb : Real.logb (m : ℝ) q ≤ 0 := (Real.logb_neg hmreal hq hq1).le
  have hpower (n : ℕ) : ((m : ℝ) ^ n) ^ Real.logb (m : ℝ) q = q ^ n := by
    rw [← Real.rpow_pow_comm hmpos.le, Real.rpow_logb hmpos (ne_of_gt hmreal) hq]
  have hup := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (r : ℝ) + 1) hupper_real hb
  rw [hpower, pow_succ] at hup
  have hlo := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (m : ℝ) ^ L) hlower_real hb
  rw [hpower, Real.mul_rpow hmpos.le (by positivity),
    Real.rpow_logb hmpos (ne_of_gt hmreal) hq] at hlo
  rw [hlog]
  unfold monkeyWordProb
  change q * (1 - m * q) * ((r : ℝ) + 1) ^ Real.logb (m : ℝ) q ≤
      q ^ L * (1 - m * q) ∧
    q ^ L * (1 - m * q) ≤ (1 - m * q) / q * ((r : ℝ) + 1) ^ Real.logb (m : ℝ) q
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hlo hS.le]
  · rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_right hup hS.le]

#print axioms solution

example  (m : ℕ) (hm : 2 ≤ m) (q : ℝ) (hq : 0 < q) (hmq : (m : ℝ) * q < 1)
    (e : ℕ → List (Fin m)) (he_inj : Function.Injective e)
    (he_range : Set.range e = {w | w ≠ []})
    (he_sorted : Antitone (fun r => monkeyWordProb m q (e r))) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ r : ℕ,
      C₁ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) ≤ monkeyWordProb m q (e r) ∧
        monkeyWordProb m q (e r) ≤ C₂ * ((r : ℝ) + 1) ^ (-Real.logb m (1 / q)) := solution m hm q hq hmq e he_inj he_range he_sorted

end ZipfAudit.monkey_typing_power_law

namespace ZipfAudit.yuleSimon_tail

set_option autoImplicit false

open ZipfLaw Filter Topology

private lemma zipf_gamma_product (a : ℝ) (ha : 0 < a) (n : ℕ) :
    Real.Gamma (a + n + 1) = Real.Gamma a * ∏ j ∈ Finset.range (n + 1), (a + j) := by
  induction n with
  | zero => simp [Real.Gamma_add_one ha.ne', mul_comm]
  | succ n ih =>
    have hpos : 0 < a + n + 1 := by positivity
    rw [Nat.cast_succ, show a + ((n : ℝ) + 1) + 1 = (a + n + 1) + 1 by ring,
      Real.Gamma_add_one hpos.ne', ih]
    conv_rhs => rw [Finset.prod_range_succ]
    push_cast
    ring

private lemma zipf_yule_ratio (ρ : ℝ) (hρ : 0 < ρ) (k : ℕ) (hk : 1 ≤ k) :
    yuleSimonPMF ρ k / (ρ ^ 2 * Real.Gamma ρ / (k : ℝ) ^ (ρ + 1)) =
      Real.GammaSeq ρ k / Real.Gamma ρ := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hG := Real.Gamma_pos_of_pos hρ
  have hprod : (∏ j ∈ Finset.range (k + 1), (ρ + (j : ℝ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    positivity
  rw [yuleSimonPMF, Real.Gamma_add_one hρ.ne',
    show (k : ℝ) + ρ + 1 = ρ + k + 1 by ring, zipf_gamma_product ρ hρ k,
    Real.GammaSeq, ← Real.Gamma_nat_eq_factorial k, Real.Gamma_add_one hkpos.ne',
    Real.rpow_add hkpos, Real.rpow_one]
  field_simp [hρ.ne', hG.ne', hprod, (Real.rpow_pos_of_pos hkpos ρ).ne']

theorem solution (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsEquivalent Filter.atTop (fun k : ℕ => yuleSimonPMF ρ k)
        (fun k : ℕ => C / (k : ℝ) ^ (ρ + 1)) := by
  have hG := Real.Gamma_pos_of_pos hρ
  refine ⟨ρ ^ 2 * Real.Gamma ρ, by positivity, ?_⟩
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hlimit := (Real.GammaSeq_tendsto_Gamma ρ).div_const (Real.Gamma ρ)
  rw [div_self hG.ne'] at hlimit
  apply hlimit.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact (zipf_yule_ratio ρ hρ k hk).symm

#print axioms solution

example  (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
      Asymptotics.IsEquivalent Filter.atTop (fun k : ℕ => yuleSimonPMF ρ k)
        (fun k : ℕ => C / (k : ℝ) ^ (ρ + 1)) := solution ρ hρ

end ZipfAudit.yuleSimon_tail

namespace ZipfAudit.zipf_infinite_extension

set_option autoImplicit false

open ZipfLaw

private lemma harmonic_range (N : ℕ) (s : ℝ) :
    genHarmonic N s = ∑ k ∈ Finset.range N, 1 / ((k : ℝ) + 1) ^ s := by
  induction N with
  | zero => simp [genHarmonic]
  | succ N ih =>
    change (∑ k ∈ Finset.Icc 1 (N + 1), 1 / (k : ℝ) ^ s) = _
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ]
    change genHarmonic N s + 1 / ((N + 1 : ℕ) : ℝ) ^ s = _
    rw [ih]
    simp

private lemma zipf_summable_iff (s : ℝ) :
    Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s := by
  have h := Real.summable_one_div_nat_add_rpow 1 s
  have habs : ∀ k : ℕ, |(k : ℝ) + 1| = (k : ℝ) + 1 := fun k =>
    abs_of_pos (by positivity)
  simpa only [habs] using h

private lemma real_term_cast (k : ℕ) (s : ℝ) :
    ((1 / ((k : ℝ) + 1) ^ s : ℝ) : ℂ) = 1 / (k + 1 : ℂ) ^ (s : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_cpow (by positivity)]
  simp

theorem solution (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := by
  refine ⟨zipf_summable_iff s, ?_, ?_⟩
  · intro hs1
    have hreal := (zipf_summable_iff s).mpr hs1
    have hcomplex := (Complex.hasSum_ofReal).mpr hreal.hasSum
    have hcomplexSummable : Summable (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) :=
      hcomplex.summable.congr (fun k => real_term_cast k s)
    have hsum : HasSum (fun k : ℕ => 1 / (k + 1 : ℂ) ^ (s : ℂ)) (riemannZeta s) := by
      rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs1)]
      exact hcomplexSummable.hasSum
    have hfn : (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) =
        (fun N : ℕ => ∑ k ∈ Finset.range N, 1 / (k + 1 : ℂ) ^ (s : ℂ)) := by
      funext N
      rw [harmonic_range]
      simp only [Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun k _ => real_term_cast k s)
    rw [hfn]
    exact hsum.tendsto_sum_nat
  · intro hs1
    have hnot : ¬Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) := by
      rw [zipf_summable_iff]
      exact not_lt_of_ge hs1
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun k : ℕ => by positivity : ∀ k : ℕ, 0 ≤ 1 / ((k : ℝ) + 1) ^ s)).mp hnot
    simpa only [← harmonic_range] using hdiv

#print axioms solution

example  (s : ℝ) (hs : 0 ≤ s) :
    (Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ s) ↔ 1 < s) ∧
      (1 < s → Filter.Tendsto (fun N : ℕ => ((genHarmonic N s : ℝ) : ℂ)) Filter.atTop
        (nhds (riemannZeta s))) ∧
      (s ≤ 1 → Filter.Tendsto (fun N : ℕ => genHarmonic N s) Filter.atTop Filter.atTop) := solution s hs

end ZipfAudit.zipf_infinite_extension

namespace ZipfAudit.zipf_one_leadingDigit_benford

set_option autoImplicit false

open ZipfLaw Filter Topology

private noncomputable def zipf_digitWeight (d N : ℕ) : ℝ :=
  ∑ k ∈ (Finset.Ico 1 N).filter (fun k => leadingDigit k = d), 1 / (k : ℝ)

private noncomputable def zipf_digitBlock (d j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ico (d * 10 ^ j) ((d + 1) * 10 ^ j), 1 / (k : ℝ)

private lemma zipf_Ico_harmonic (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Ico 1 n, 1 / (k : ℝ)) = genHarmonic (n - 1) 1 := by
  unfold genHarmonic
  simp only [Real.rpow_one]
  rw [← Finset.Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hn]

private lemma zipf_harmonic_real (n : ℕ) : genHarmonic n 1 = (harmonic n : ℝ) := by
  induction n with
  | zero => simp [genHarmonic]
  | succ n ih =>
    unfold genHarmonic
    rw [Finset.sum_Icc_succ_top (by omega), harmonic_succ]
    push_cast
    change genHarmonic n 1 + 1 / ((n : ℝ) + 1) ^ (1 : ℝ) = _
    rw [ih]
    simp [one_div]

private lemma zipf_block_harmonic (d j : ℕ) (hd : 1 ≤ d) :
    zipf_digitBlock d j = genHarmonic ((d + 1) * 10 ^ j - 1) 1 -
      genHarmonic (d * 10 ^ j - 1) 1 := by
  have hp : 1 ≤ 10 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have ha : 1 ≤ d * 10 ^ j := by nlinarith
  have hab : d * 10 ^ j ≤ (d + 1) * 10 ^ j := by nlinarith
  have h := Finset.sum_Ico_consecutive (fun k : ℕ => 1 / (k : ℝ)) ha hab
  rw [zipf_Ico_harmonic _ ha, zipf_Ico_harmonic _ (le_trans ha hab)] at h
  unfold zipf_digitBlock
  linarith

private lemma zipf_power_blocks (d M : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    zipf_digitWeight d (10 ^ M) = ∑ j ∈ Finset.range M, zipf_digitBlock d j := by
  classical
  let T := (Finset.Ico 1 (10 ^ M)).filter (fun k => leadingDigit k = d)
  have hmap : (T : Set ℕ).MapsTo (Nat.log 10) (Finset.range M) := by
    intro k hk
    have hkI := Finset.mem_Ico.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_range.mpr
    exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hkI.2
  have hfiber (j : ℕ) (hj : j ∈ Finset.range M) :
      T.filter (fun k => Nat.log 10 k = j) = Finset.Ico (d * 10 ^ j) ((d + 1) * 10 ^ j) := by
    have hjM : j < M := Finset.mem_range.mp hj
    have hp : 0 < 10 ^ j := by positivity
    ext k
    simp only [T, Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hkI, hlead⟩, hlog⟩
      have hdiv : k / 10 ^ j = d := by simpa only [leadingDigit, hlog] using hlead
      constructor
      · simpa only [hdiv] using Nat.div_mul_le_self k (10 ^ j)
      · apply (Nat.div_lt_iff_lt_mul hp).mp
        omega
    · intro hk
      have hkp : 10 ^ j ≤ k := by nlinarith [Nat.one_le_iff_ne_zero.mpr hp.ne']
      have hk10 : k < 10 ^ (j + 1) := by
        rw [pow_succ]
        nlinarith
      have hlog : Nat.log 10 k = j := Nat.log_eq_of_pow_le_of_lt_pow hkp hk10
      have hk1 : 1 ≤ k := le_trans (by omega) hkp
      have hkM : k < 10 ^ M := lt_of_lt_of_le hk10
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) (by omega))
      have hdivlo : d ≤ k / 10 ^ j := (Nat.le_div_iff_mul_le hp).mpr hk.1
      have hdivhi : k / 10 ^ j < d + 1 := (Nat.div_lt_iff_lt_mul hp).mpr hk.2
      refine ⟨⟨⟨hk1, hkM⟩, ?_⟩, hlog⟩
      unfold leadingDigit
      rw [hlog]
      omega
  unfold zipf_digitWeight
  change (∑ k ∈ T, 1 / (k : ℝ)) = _
  rw [← Finset.sum_fiberwise_of_maps_to hmap (fun k : ℕ => 1 / (k : ℝ))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hfiber j hj]
  rfl

private lemma zipf_cutoff_atTop (a : ℕ) (ha : 1 ≤ a) :
    Tendsto (fun j : ℕ => a * 10 ^ j - 1) atTop atTop := by
  have hpr : Tendsto (fun j : ℕ => (10 : ℝ) ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hp : Tendsto (fun j : ℕ => (10 : ℕ) ^ j) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hpr)
  have hmul : Tendsto (fun j : ℕ => a * 10 ^ j) atTop atTop := by
    apply tendsto_atTop_mono _ hp
    intro j
    simpa only [one_mul] using Nat.mul_le_mul_right (10 ^ j) ha
  exact (tendsto_sub_atTop_nat 1).comp hmul

private lemma zipf_log_cutoff (a j : ℕ) (ha : 1 ≤ a) :
    Real.log (((a * 10 ^ j - 1 : ℕ) : ℝ) + 1) =
      Real.log (a : ℝ) + (j : ℝ) * Real.log 10 := by
  have hp : 1 ≤ 10 ^ j := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hap : 1 ≤ a * 10 ^ j := by nlinarith
  have heq : (((a * 10 ^ j - 1 : ℕ) : ℝ) + 1) = (a : ℝ) * (10 : ℝ) ^ j := by
    calc
      _ = (((a * 10 ^ j - 1) + 1 : ℕ) : ℝ) := by push_cast; rfl
      _ = ((a * 10 ^ j : ℕ) : ℝ) := by rw [Nat.sub_add_cancel hap]
      _ = _ := by push_cast; rfl
  rw [heq]
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]

private lemma zipf_block_limit (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (zipf_digitBlock d) atTop
      (nhds (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))) := by
  have ha := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop d hd)
  have hb := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop (d + 1) (by omega))
  have h := (hb.sub ha).add_const (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))
  simp only [sub_self, zero_add] at h
  apply h.congr
  intro j
  dsimp only [Function.comp_apply]
  rw [← zipf_harmonic_real, ← zipf_harmonic_real, zipf_log_cutoff _ _ (by omega),
    zipf_log_cutoff _ _ hd, zipf_block_harmonic _ _ hd]
  push_cast
  ring

private lemma zipf_weight_limit (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Tendsto (fun M : ℕ => zipf_digitWeight d (10 ^ M) / (M : ℝ)) atTop
      (nhds (Real.log ((d : ℝ) + 1) - Real.log (d : ℝ))) := by
  simpa only [zipf_power_blocks d _ hd1 hd9, div_eq_mul_inv, mul_comm] using
    (zipf_block_limit d hd1).cesaro

private lemma zipf_normalizer_limit :
    Tendsto (fun M : ℕ => genHarmonic (10 ^ M - 1) 1 / (M : ℝ)) atTop
      (nhds (Real.log 10)) := by
  have he := Real.tendsto_harmonic_sub_log_add_one.comp (zipf_cutoff_atTop 1 (by norm_num))
  have herr : Tendsto (fun M : ℕ => genHarmonic (10 ^ M - 1) 1 - (M : ℝ) * Real.log 10)
      atTop (nhds Real.eulerMascheroniConstant) := by
    apply he.congr
    intro M
    dsimp only [Function.comp_apply]
    rw [one_mul, ← zipf_harmonic_real]
    simpa only [one_mul, Nat.cast_one, Real.log_one, zero_add] using
      congrArg (fun x => genHarmonic (10 ^ M - 1) 1 - x) (zipf_log_cutoff 1 M (by norm_num))
  have h := (herr.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))).add_const (Real.log 10)
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  field_simp
  <;> ring

private lemma zipf_shift_quotient {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto (fun M : ℕ => f M / (M : ℝ)) atTop (nhds c)) :
    Tendsto (fun M : ℕ => f (M + 1) / (M : ℝ)) atTop (nhds c) := by
  have hr : Tendsto (fun M : ℕ => ((M : ℝ) + 1) / (M : ℝ)) atTop (nhds (1 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have h' := h.const_add 1
    simp only [add_zero] at h'
    apply h'.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    field_simp
  have h := (hf.comp (tendsto_add_atTop_nat 1)).mul hr
  simp only [mul_one] at h
  apply h.congr
  intro M
  dsimp only [Function.comp_apply]
  rw [Nat.cast_add, Nat.cast_one, ← mul_div_assoc,
    div_mul_cancel₀ _ (show (M : ℝ) + 1 ≠ 0 by positivity)]

private lemma zipf_weight_mono (d : ℕ) : Monotone (zipf_digitWeight d) := by
  intro N M hNM
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have h := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr
      ⟨(Finset.mem_Ico.mp h.1).1, lt_of_lt_of_le (Finset.mem_Ico.mp h.1).2 hNM⟩, h.2⟩
  · intro k _ _
    positivity

private lemma zipf_harmonic_mono : Monotone (fun N : ℕ => genHarmonic N 1) := by
  intro N M hNM
  unfold genHarmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have h := Finset.mem_Icc.mp hk
    exact Finset.mem_Icc.mpr ⟨h.1, le_trans h.2 hNM⟩
  · intro k _ _
    positivity

private lemma zipf_harmonic_positive (N : ℕ) (hN : 1 ≤ N) : 0 < genHarmonic N 1 := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity) ⟨1, by simp [hN], by norm_num⟩

private lemma zipf_nat_log_atTop : Tendsto (fun N : ℕ => Nat.log 10 (N + 1)) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (10 ^ b)] with N hN
  exact Nat.le_log_of_pow_le (by norm_num) (by omega)

private lemma zipf_digit_probability (d N : ℕ) :
    (∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k) =
      zipf_digitWeight d (N + 1) / genHarmonic N 1 := by
  unfold zipf_digitWeight
  rw [Finset.Ico_add_one_right_eq_Icc, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1), Real.rpow_one]

theorem solution (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k)
      Filter.atTop (nhds (Real.logb 10 (1 + 1 / (d : ℝ)))) := by
  let c := Real.log ((d : ℝ) + 1) - Real.log (d : ℝ)
  let A := fun M : ℕ => zipf_digitWeight d (10 ^ M)
  let H := fun M : ℕ => genHarmonic (10 ^ M - 1) 1
  have hA : Tendsto (fun M : ℕ => A M / (M : ℝ)) atTop (nhds c) :=
    zipf_weight_limit d hd1 hd9
  have hH : Tendsto (fun M : ℕ => H M / (M : ℝ)) atTop (nhds (Real.log 10)) :=
    zipf_normalizer_limit
  have hlog : Real.log (10 : ℝ) ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlower : Tendsto (fun M : ℕ => A M / H (M + 1)) atTop (nhds (c / Real.log 10)) := by
    have h := hA.div (zipf_shift_quotient hH) hlog
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    exact div_div_div_cancel_right₀ (by exact_mod_cast (show M ≠ 0 by omega)) _ _
  have hupper : Tendsto (fun M : ℕ => A (M + 1) / H M) atTop (nhds (c / Real.log 10)) := by
    have h := (zipf_shift_quotient hA).div hH hlog
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    exact div_div_div_cancel_right₀ (by exact_mod_cast (show M ≠ 0 by omega)) _ _
  have hprob : Tendsto (fun N : ℕ => zipf_digitWeight d (N + 1) / genHarmonic N 1)
      atTop (nhds (c / Real.log 10)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (hlower.comp zipf_nat_log_atTop) (hupper.comp zipf_nat_log_atTop)
    · filter_upwards [zipf_nat_log_atTop.eventually (eventually_ge_atTop 1)] with N hM
      let M := Nat.log 10 (N + 1)
      have hlo : 10 ^ M ≤ N + 1 := Nat.pow_log_le_self 10 (by omega)
      have hhi : N + 1 < 10 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hP : 1 < 10 ^ M := lt_of_lt_of_le (by norm_num : 1 < (10 : ℕ) ^ 1)
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) hM)
      have hN : 1 ≤ N := by omega
      have hn := zipf_harmonic_positive N hN
      have hH1 : 0 < H (M + 1) := zipf_harmonic_positive _ (by
        have := pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) (Nat.le_succ M)
        omega)
      have hnon : 0 ≤ zipf_digitWeight d (N + 1) := Finset.sum_nonneg (fun _ _ => by positivity)
      change A M / H (M + 1) ≤ _
      calc
        _ ≤ zipf_digitWeight d (N + 1) / H (M + 1) :=
          div_le_div_of_nonneg_right (zipf_weight_mono d hlo) hH1.le
        _ ≤ _ := div_le_div_of_nonneg_left hnon hn (zipf_harmonic_mono (by omega))
    · filter_upwards [zipf_nat_log_atTop.eventually (eventually_ge_atTop 1)] with N hM
      let M := Nat.log 10 (N + 1)
      have hlo : 10 ^ M ≤ N + 1 := Nat.pow_log_le_self 10 (by omega)
      have hhi : N + 1 < 10 ^ (M + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hP : 1 < 10 ^ M := lt_of_lt_of_le (by norm_num : 1 < (10 : ℕ) ^ 1)
        (pow_le_pow_right₀ (by norm_num : 1 ≤ (10 : ℕ)) hM)
      have hN : 1 ≤ N := by omega
      have hn := zipf_harmonic_positive N hN
      have hH0 : 0 < H M := zipf_harmonic_positive _ (by omega)
      have hnon : 0 ≤ A (M + 1) := Finset.sum_nonneg (fun _ _ => by positivity)
      change _ ≤ A (M + 1) / H M
      calc
        _ ≤ A (M + 1) / genHarmonic N 1 :=
          div_le_div_of_nonneg_right (zipf_weight_mono d hhi.le) hn.le
        _ ≤ _ := div_le_div_of_nonneg_left hnon hH0 (zipf_harmonic_mono (by omega))
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hvalue : c / Real.log 10 = Real.logb 10 (1 + 1 / (d : ℝ)) := by
    rw [Real.logb, show 1 + 1 / (d : ℝ) = ((d : ℝ) + 1) / d by field_simp,
      Real.log_div (by positivity) hdpos.ne']
  rw [hvalue] at hprob
  simpa only [zipf_digit_probability] using hprob

#print axioms solution

example  (d : ℕ) (hd1 : 1 ≤ d) (hd9 : d ≤ 9) :
    Filter.Tendsto
      (fun N : ℕ => ∑ k ∈ (Finset.Icc 1 N).filter (fun k => leadingDigit k = d), zipfPMF N 1 k)
      Filter.atTop (nhds (Real.logb 10 (1 + 1 / (d : ℝ)))) := solution d hd1 hd9

end ZipfAudit.zipf_one_leadingDigit_benford

namespace ZipfAudit.zipfMandelbrotPMF_hasSum_one

set_option autoImplicit false

open ZipfLaw

theorem solution (q s : ℝ) (hq : 0 ≤ q) (hs : 1 < s) :
    HasSum (fun k : ℕ => zipfMandelbrotPMF q s k) 1 := by
  have hq1 : 0 < q + 1 := by linarith
  have habs (n : ℕ) : |(n : ℝ) + (q + 1)| = (n : ℝ) + (q + 1) :=
    abs_of_pos (by positivity)
  have hsum : Summable (fun n : ℕ => 1 / ((n : ℝ) + (q + 1)) ^ s) := by
    simpa only [habs] using (Real.summable_one_div_nat_add_rpow (q + 1) s).mpr hs
  have hC : 0 < hurwitzZetaSeries s (q + 1) := by
    exact hsum.tsum_pos (fun n => by positivity) 0 (by positivity)
  have hscaled : HasSum
      (fun n : ℕ => (1 / ((n : ℝ) + (q + 1)) ^ s) / hurwitzZetaSeries s (q + 1)) 1 := by
    have hseries : HasSum (fun n : ℕ => 1 / ((n : ℝ) + (q + 1)) ^ s)
        (hurwitzZetaSeries s (q + 1)) := hsum.hasSum
    simpa only [div_self hC.ne'] using
      hseries.div_const (hurwitzZetaSeries s (q + 1))
  have hshift : HasSum (fun n : ℕ => zipfMandelbrotPMF q s (n + 1)) 1 := by
    convert hscaled using 1
    funext n
    rw [zipfMandelbrotPMF, if_pos (by omega)]
    push_cast
    rw [show (n : ℝ) + 1 + q = (n : ℝ) + (q + 1) by ring]
    ring
  have hz : zipfMandelbrotPMF q s 0 = 0 := by simp [zipfMandelbrotPMF]
  have hshift' : HasSum (fun n : ℕ => zipfMandelbrotPMF q s (n + 1))
      (1 - ∑ k ∈ Finset.range 1, zipfMandelbrotPMF q s k) := by
    simpa only [Finset.sum_range_one, hz, sub_zero] using hshift
  exact (hasSum_nat_add_iff' 1).mp hshift'

#print axioms solution

example  (q s : ℝ) (hq : 0 ≤ q) (hs : 1 < s) :
    HasSum (fun k : ℕ => zipfMandelbrotPMF q s k) 1 := solution q s hq hs

end ZipfAudit.zipfMandelbrotPMF_hasSum_one

namespace ZipfAudit.zipfPMF_cdf

set_option autoImplicit false

open ZipfLaw

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, zipfPMF N s k = genHarmonic n s / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  exact Finset.sum_congr rfl (fun k hk => by
    rw [zipfPMF, if_pos ⟨(Finset.mem_Icc.mp hk).1, le_trans (Finset.mem_Icc.mp hk).2 hn⟩])

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (n : ℕ) (hn : n ≤ N) :
    ∑ k ∈ Finset.Icc 1 n, zipfPMF N s k = genHarmonic n s / genHarmonic N s := solution N hN s n hn

end ZipfAudit.zipfPMF_cdf

namespace ZipfAudit.zipfPMF_entropy

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

private lemma log_term (N : ℕ) (s : ℝ) (k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ N) :
    Real.log (zipfPMF N s k) = -s * Real.log k - Real.log (genHarmonic N s) := by
  have hH := zipf_harmonic_pos N (le_trans hk1 hkN) s
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hp := Real.rpow_pos_of_pos hkpos s
  rw [zipfPMF, if_pos ⟨hk1, hkN⟩, Real.log_div (by positivity) hH.ne',
    Real.log_div (by norm_num) hp.ne', Real.log_one, Real.log_rpow hkpos]
  ring

private lemma pmf_sum (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  have hH := zipf_harmonic_pos N hN s
  calc
    (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ s) / genHarmonic N s := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)])
    _ = 1 := div_self (ne_of_gt hH)

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    -(∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
      s / genHarmonic N s * (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) +
        Real.log (genHarmonic N s) := by
  have hsum :
      (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
        -s * (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log k) -
          Real.log (genHarmonic N s) * (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) := by
    calc
      _ = ∑ k ∈ Finset.Icc 1 N,
          ((-s) * (zipfPMF N s k * Real.log k) -
            Real.log (genHarmonic N s) * zipfPMF N s k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [log_term N s k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2]
        ring
      _ = _ := by simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hweighted :
      (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log k) =
        (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) / genHarmonic N s := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)]
    ring
  rw [hsum, hweighted, pmf_sum N hN s]
  ring

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    -(∑ k ∈ Finset.Icc 1 N, zipfPMF N s k * Real.log (zipfPMF N s k)) =
      s / genHarmonic N s * (∑ k ∈ Finset.Icc 1 N, Real.log k / (k : ℝ) ^ s) +
        Real.log (genHarmonic N s) := solution N hN s

end ZipfAudit.zipfPMF_entropy

namespace ZipfAudit.zipfPMF_mean

set_option autoImplicit false

open ZipfLaw

private lemma moment_sum (N : ℕ) (s : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ p * zipfPMF N s k) =
      genHarmonic N (s - p) / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    exact_mod_cast this
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk), Real.rpow_sub hkpos, Real.rpow_natCast]
  simp only [one_div_div]
  ring

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k =
      genHarmonic N (s - 1) / genHarmonic N s := by
  simpa only [Nat.cast_one, pow_one] using moment_sum N s 1

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k = genHarmonic N (s - 1) / genHarmonic N s := solution N hN s

end ZipfAudit.zipfPMF_mean

namespace ZipfAudit.zipfPMF_mode

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := by
  have hH := zipf_harmonic_pos N hN s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  rw [h1]
  by_cases hk : 1 ≤ k ∧ k ≤ N
  · rw [zipfPMF, if_pos hk]
    apply div_le_div_of_nonneg_right _ (le_of_lt hH)
    have hbase : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    simpa using one_div_le_one_div_of_le zero_lt_one (Real.one_le_rpow hbase hs)
  · rw [zipfPMF, if_neg hk]
    exact div_nonneg zero_le_one (le_of_lt hH)

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) (hs : 0 ≤ s) (k : ℕ) :
    zipfPMF N s k ≤ zipfPMF N s 1 := solution N hN s hs k

end ZipfAudit.zipfPMF_mode

namespace ZipfAudit.zipfPMF_ratio

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := by
  have hN : 1 ≤ N := le_trans hn1 hnN
  have hH := zipf_harmonic_pos N hN s
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hp := Real.rpow_pos_of_pos hnpos s
  have h1 : zipfPMF N s 1 = 1 / genHarmonic N s := by simp [zipfPMF, hN]
  rw [h1, zipfPMF, if_pos ⟨hn1, hnN⟩]
  field_simp [ne_of_gt hH, ne_of_gt hp] <;> ring

#print axioms solution


example  (N : ℕ) (s : ℝ) (n : ℕ) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    zipfPMF N s 1 / zipfPMF N s n = (n : ℝ) ^ s := solution N s n hn1 hnN

end ZipfAudit.zipfPMF_ratio

namespace ZipfAudit.zipfPMF_sum_eq_one

set_option autoImplicit false

open ZipfLaw

private lemma zipf_harmonic_pos (N : ℕ) (hN : 1 ≤ N) (s : ℝ) : 0 < genHarmonic N s := by
  unfold genHarmonic
  exact Finset.sum_pos' (fun k _ => by positivity)
    ⟨1, by simp [hN], by norm_num⟩

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := by
  have hH := zipf_harmonic_pos N hN s
  calc
    (∑ k ∈ Finset.Icc 1 N, zipfPMF N s k) =
        (∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ^ s) / genHarmonic N s := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl (fun k hk => by
        rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk)])
    _ = 1 := div_self (ne_of_gt hH)

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    ∑ k ∈ Finset.Icc 1 N, zipfPMF N s k = 1 := solution N hN s

end ZipfAudit.zipfPMF_sum_eq_one

namespace ZipfAudit.zipfPMF_variance

set_option autoImplicit false

open ZipfLaw

private lemma moment_sum (N : ℕ) (s : ℝ) (p : ℕ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ p * zipfPMF N s k) =
      genHarmonic N (s - p) / genHarmonic N s := by
  rw [genHarmonic, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hk).1
    exact_mod_cast this
  rw [zipfPMF, if_pos (Finset.mem_Icc.mp hk), Real.rpow_sub hkpos, Real.rpow_natCast]
  simp only [one_div_div]
  ring

theorem solution (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := by
  have hfirst := moment_sum N s 1
  simp only [Nat.cast_one, pow_one] at hfirst
  rw [moment_sum N s 2, hfirst, div_pow]
  norm_num

#print axioms solution


example  (N : ℕ) (hN : 1 ≤ N) (s : ℝ) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ 2 * zipfPMF N s k) -
        (∑ k ∈ Finset.Icc 1 N, (k : ℝ) * zipfPMF N s k) ^ 2 =
      genHarmonic N (s - 2) / genHarmonic N s -
        genHarmonic N (s - 1) ^ 2 / genHarmonic N s ^ 2 := solution N hN s

end ZipfAudit.zipfPMF_variance
