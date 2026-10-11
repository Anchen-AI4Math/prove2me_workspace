import missions.zeta9.formalization.CoefficientMapAggregate

/-!
Actual cumulative partial fractions for a zero vector of the five-dimensional map.
The telescoper is built from the true local coefficients, not assumed to exist.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapTelescoper

open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate

def prefixSum (c : ℕ → ℚ) (j : ℕ) : ℚ := ∑ i ∈ range (j + 1), c i

def cumulativeCoefficient (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  prefixSum (fun i => weightedLocalCoefficient n i s W) j

def telescoper (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9, cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s

def telescoperNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
    C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s

def rootNode (n : ℕ) (i : Fin (n + 1) ⊕ Fin (n + 1)) : ℚ :=
  match i with
  | .inl k => (k.val : ℚ) + 1
  | .inr k => -(n : ℚ) - (k.val : ℚ)

def rootPolynomial (n : ℕ) : ℚ[X] :=
  ∏ i : Fin (n + 1) ⊕ Fin (n + 1), (X - C (rootNode n i))

theorem prefixSum_succ (c : ℕ → ℚ) (j : ℕ) :
    prefixSum c (j + 1) = prefixSum c j + c (j + 1) := by
  unfold prefixSum
  exact Finset.sum_range_succ _ _

theorem finite_cumulative_difference (n : ℕ) (c f : ℕ → ℚ) :
    (∑ j ∈ range n, prefixSum c j * (f j - f (j + 1))) =
      (∑ j ∈ range (n + 1), c j * f j) - prefixSum c n * f n := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [Finset.sum_range_succ (fun j => prefixSum c j * (f j - f (j + 1))) n, ih,
      Finset.sum_range_succ (fun j => c j * f j) (n + 1), prefixSum_succ]
    ring

theorem cumulativeCoefficient_succ (n j s : ℕ) (W : ℚ[X]) :
    cumulativeCoefficient n (j + 1) s W = cumulativeCoefficient n j s W +
      weightedLocalCoefficient n (j + 1) s W := prefixSum_succ _ j

theorem cumulativeCoefficient_last_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (s : ℕ) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) : cumulativeCoefficient n n s W = 0 :=
  aggregate_zero_all_rho n hn W hstrong hzero s hs1 hs9

theorem telescoper_as_sum_over_orders (n : ℕ) (W : ℚ[X]) (t : ℚ) :
    telescoper n W t = ∑ s ∈ Icc 1 9, ∑ j ∈ range n,
      cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s := Finset.sum_comm

theorem telescoper_difference_principal_parts (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W t - telescoper n W (t + 1) =
      ∑ j ∈ range (n + 1), ∑ s ∈ Icc 1 9,
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
  rw [telescoper_as_sum_over_orders, telescoper_as_sum_over_orders, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range n, cumulativeCoefficient n j s W *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s) := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      have hshift : (t + 1) + (j : ℚ) = t + ((j + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [hshift]
      ring
    _ = ∑ s ∈ Icc 1 9, ∑ j ∈ range (n + 1),
        weightedLocalCoefficient n j s W / (t + (j : ℚ)) ^ s := by
      apply Finset.sum_congr rfl
      intro s hs
      have h := finite_cumulative_difference n (fun j => weightedLocalCoefficient n j s W)
        (fun j => 1 / (t + (j : ℚ)) ^ s)
      change (∑ j ∈ range n, prefixSum (fun j => weightedLocalCoefficient n j s W) j *
        (1 / (t + (j : ℚ)) ^ s - 1 / (t + ((j + 1 : ℕ) : ℚ)) ^ s)) = _
      rw [h]
      have htotal : prefixSum (fun j => weightedLocalCoefficient n j s W) n = 0 :=
        cumulativeCoefficient_last_zero n hn W hstrong hzero s (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
      simp only [htotal, mul_one_div, zero_div, sub_zero]
    _ = _ := Finset.sum_comm

theorem actual_weightedR_is_difference (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ)
    (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    CoefficientMap.weightedR n W t = telescoper n W t - telescoper n W (t + 1) := by
  rw [telescoper_difference_principal_parts n hn W hstrong hzero t]
  exact CoefficientMapPartialFractions.actual_global_partial_fractions n W
    (strong_proper_implies_proper n W hstrong) t hregular

theorem telescoper_positive_tendsto_zero (n : ℕ) (W : ℚ[X]) :
    Tendsto (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (range n) (fun j hj => tendsto_finsetSum (Icc 1 9) (fun s hs =>
    (CoefficientMapSummation.shifted_reciprocal_tendsto_zero s (j + 1) (Finset.mem_Icc.mp hs).1).const_mul
      (cumulativeCoefficient n j s W : ℝ)))
  have he : (fun T : ℕ => (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) =
      (fun T : ℕ => ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
        (cumulativeCoefficient n j s W : ℝ) * (1 / ((T : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ s)) := by
    funext T
    unfold telescoper
    push_cast
    simp only [mul_one_div, add_left_comm, add_comm]
  rw [he]
  simpa only [mul_zero, Finset.sum_const_zero] using h

theorem finite_sum_is_telescoper_boundary (n T : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    CoefficientMapFiniteSum.finiteL n T W = telescoper n W 1 - telescoper n W ((T + 1 : ℕ) : ℚ) := by
  induction T with
  | zero => simp [CoefficientMapFiniteSum.finiteL]
  | succ T ih =>
    have hstep : CoefficientMapFiniteSum.finiteL n (T + 1) W =
        CoefficientMapFiniteSum.finiteL n T W + CoefficientMap.weightedR n W ((T + 1 : ℕ) : ℚ) := by
      unfold CoefficientMapFiniteSum.finiteL
      exact Finset.sum_Icc_succ_top (by omega) _
    rw [hstep, ih, actual_weightedR_is_difference n hn W hstrong hzero]
    · have he : ((T + 1 : ℕ) : ℚ) + 1 = ((T + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he]
      ring
    · intro k hk
      exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k))

theorem telescoper_at_one_zero (n : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) : telescoper n W 1 = 0 := by
  have hfinite := CoefficientMapSummation.actual_finiteL_tendsto_exactL n hn W hstrong
  rw [aggregate_zero_exactL n W hzero] at hfinite
  have hboundary := (tendsto_const_nhds (x := (telescoper n W 1 : ℝ))).sub
    (telescoper_positive_tendsto_zero n W)
  have he : (fun T : ℕ => (CoefficientMapFiniteSum.finiteL n T W : ℝ)) =
      (fun T : ℕ => (telescoper n W 1 : ℝ) - (telescoper n W ((T + 1 : ℕ) : ℚ) : ℝ)) := by
    funext T
    rw [finite_sum_is_telescoper_boundary n T hn W hstrong hzero]
    push_cast
    rfl
  rw [he] at hfinite
  have h := tendsto_nhds_unique hfinite hboundary
  simp only [sub_zero] at h
  exact_mod_cast h.symm

theorem actual_weightedR_positive_zero (n k : ℕ) (W : ℚ[X]) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    CoefficientMap.weightedR n W (k : ℚ) = 0 := by
  have hprod : (∏ i ∈ range n, ((k : ℚ) - ((i : ℚ) + 1))) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (show k - 1 < n by omega))
    have he : k - 1 + 1 = k := by omega
    exact sub_eq_zero.mpr (by exact_mod_cast he.symm)
  simp [CoefficientMap.weightedR, CoefficientMap.actualR, CoefficientMap.numerator, hprod]

theorem telescoper_positive_zeros (n k : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) : telescoper n W (k : ℚ) = 0 := by
  have hzeros : ∀ l ≤ n, telescoper n W ((l + 1 : ℕ) : ℚ) = 0 := by
    intro l
    induction l with
    | zero => intro hl; exact telescoper_at_one_zero n hn W hstrong hzero
    | succ l ih =>
      intro hl
      have hprev := ih (by omega)
      have hdiff := actual_weightedR_is_difference n hn W hstrong hzero ((l + 1 : ℕ) : ℚ)
        (by intro k hk; exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (Nat.cast_nonneg k)))
      rw [actual_weightedR_positive_zero n (l + 1) W (by omega) (by omega), hprev] at hdiff
      have he : ((l + 1 : ℕ) : ℚ) + 1 = ((l + 1 + 1 : ℕ) : ℚ) := by push_cast; ring
      rw [he] at hdiff
      linarith
  have he : k - 1 + 1 = k := by omega
  simpa only [he] using hzeros (k - 1) (by omega)

theorem cumulativeCoefficient_reflection (n j s : ℕ) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (hj : j < n) (hs1 : 1 ≤ s) (hs9 : s ≤ 9) :
    cumulativeCoefficient n (n - 1 - j) s W = (-1 : ℚ) ^ s * cumulativeCoefficient n j s W := by
  induction j with
  | zero =>
    have hn1 : 1 ≤ n := by omega
    have hlast := cumulativeCoefficient_last_zero n hn W hstrong hzero s hs1 hs9
    have hstep := cumulativeCoefficient_succ n (n - 1) s W
    rw [show n - 1 + 1 = n by omega, hlast] at hstep
    have hreflection := local_coefficient_reflection n 0 s hn W (by omega) hs1 hs9
    simp only [Nat.sub_zero, pow_succ] at hreflection
    simp only [Nat.sub_zero]
    have hfirst : cumulativeCoefficient n 0 s W = weightedLocalCoefficient n 0 s W := by
      simp [cumulativeCoefficient, prefixSum]
    rw [hfirst]
    rw [hreflection] at hstep
    nlinarith
  | succ j ih =>
    have hprev := ih (by omega)
    have hstep := cumulativeCoefficient_succ n (n - 1 - (j + 1)) s W
    rw [show n - 1 - (j + 1) + 1 = n - 1 - j by omega, hprev] at hstep
    have hreflection := local_coefficient_reflection n (j + 1) s hn W (by omega) hs1 hs9
    rw [show n - (j + 1) = n - 1 - j by omega] at hreflection
    rw [hreflection, pow_succ] at hstep
    rw [cumulativeCoefficient_succ]
    nlinarith

theorem telescoper_reflection (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (t : ℚ) :
    telescoper n W (1 - (n : ℚ) - t) = telescoper n W t := by
  have hreverse := sum_reverse_range (n - 1)
    (fun j => ∑ s ∈ Icc 1 9,
      cumulativeCoefficient n j s W / ((1 - (n : ℚ) - t) + (j : ℚ)) ^ s)
  rw [show n - 1 + 1 = n by omega] at hreverse
  unfold telescoper
  rw [← hreverse]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn := Finset.mem_range.mp hj
  apply Finset.sum_congr rfl
  intro s hs
  rw [cumulativeCoefficient_reflection n j s hn W hstrong hzero hjn
    (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2]
  have he : (1 - (n : ℚ) - t) + ((n - 1 - j : ℕ) : ℚ) = -(t + (j : ℚ)) := by
    have hnsub : (n - 1 - j : ℕ) + (j + 1) = n := by omega
    have hc : ((n - 1 - j : ℕ) : ℚ) + ((j : ℚ) + 1) = (n : ℚ) := by exact_mod_cast hnsub
    linarith
  rw [he, neg_pow (t + (j : ℚ))]
  exact mul_div_mul_left _ _ (pow_ne_zero s (by norm_num : (-1 : ℚ) ≠ 0))

theorem telescoper_negative_zeros (n k : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) (hk : k ≤ n) :
    telescoper n W (-(n : ℚ) - (k : ℚ)) = 0 := by
  have hreflection := telescoper_reflection n hn1 hn W hstrong hzero (-(n : ℚ) - (k : ℚ))
  have he : 1 - (n : ℚ) - (-(n : ℚ) - (k : ℚ)) = ((k + 1 : ℕ) : ℚ) := by push_cast; ring
  rw [he, telescoper_positive_zeros n (k + 1) hn W hstrong hzero (by omega) (by omega)] at hreflection
  exact hreflection.symm

theorem cleared_term_division (n j s : ℕ) (a t : ℚ) (hj : j ≤ n)
    (hs1 : 1 ≤ s) (hs9 : s ≤ 9) (hregular : ∀ k ≤ n, t + (k : ℚ) ≠ 0) :
    (a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      (t + (j : ℚ)) ^ (9 - s)) / (polePolynomial n).eval t ^ 9 = a / (t + (j : ℚ)) ^ s := by
  apply (div_eq_div_iff
    (pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero n t hregular))
    (pow_ne_zero _ (hregular j hj))).mpr
  rw [CoefficientMapPartialFractions.polePolynomial_eval_factor n j t hj, mul_pow]
  have he : (t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s = (t + (j : ℚ)) ^ 9 := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ = a * (CoefficientMapPartialFractions.clearedPolePolynomial n j).eval t ^ 9 *
      ((t + (j : ℚ)) ^ (9 - s) * (t + (j : ℚ)) ^ s) := by ring
    _ = _ := by rw [he]; ring

theorem telescoper_actual_rational_representation (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) (t : ℚ)
    (hregular : ∀ k < n, t + (k : ℚ) ≠ 0) :
    telescoper n W t = (telescoperNumerator n W).eval t / (polePolynomial (n - 1)).eval t ^ 9 := by
  symm
  simp only [telescoperNumerator, partialBasis, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro s hs
  simpa only [mul_assoc] using cleared_term_division (n - 1) j s (cumulativeCoefficient n j s W) t
    (by have := Finset.mem_range.mp hj; omega) (Finset.mem_Icc.mp hs).1 (Finset.mem_Icc.mp hs).2
    (by intro k hk; exact hregular k (by omega))

theorem telescoperNumerator_natDegree_le (n : ℕ) (hn1 : 1 ≤ n) (W : ℚ[X]) :
    (telescoperNumerator n W).natDegree ≤ 9 * n - 1 := by
  unfold telescoperNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s hs
  have h : (C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s).natDegree ≤
      (C (cumulativeCoefficient n j s W)).natDegree + (partialBasis (n - 1) j s).natDegree :=
    Polynomial.natDegree_mul_le
  rw [Polynomial.natDegree_C, zero_add,
    partialBasis_natDegree (n - 1) j s (by have := Finset.mem_range.mp hj; omega)] at h
  have horder := Finset.mem_Icc.mp hs
  omega

theorem rootNode_injective (n : ℕ) : Function.Injective (rootNode n) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simpa [rootNode] using h
      exact_mod_cast he
    | inr b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
  | inr a =>
    cases b with
    | inl b =>
      have ha : (0 : ℚ) ≤ (a.val : ℚ) := Nat.cast_nonneg _
      have hb : (0 : ℚ) ≤ (b.val : ℚ) := Nat.cast_nonneg _
      have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg _
      simp only [rootNode] at h
      linarith
    | inr b =>
      congr 1
      apply Fin.ext
      have he : (a.val : ℚ) = (b.val : ℚ) := by simp only [rootNode] at h; linarith
      exact_mod_cast he

theorem rootPolynomial_monic (n : ℕ) : (rootPolynomial n).Monic := by
  unfold rootPolynomial
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact Polynomial.monic_X_sub_C _

theorem rootPolynomial_eq_explicit_products (n : ℕ) :
    rootPolynomial n =
      (∏ k ∈ range (n + 1), (X - C ((k : ℚ) + 1))) *
      (∏ k ∈ range (n + 1), (X + C (n : ℚ) + C (k : ℚ))) := by
  unfold rootPolynomial
  rw [Fintype.prod_sum_type]
  simp only [rootNode]
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C ((k : ℚ) + 1) : ℚ[X])) (n + 1),
    Fin.prod_univ_eq_prod_range (fun k : ℕ => (X - C (-(n : ℚ) - (k : ℚ)) : ℚ[X])) (n + 1)]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  simp only [map_sub, map_neg]
  ring

theorem rootPolynomial_natDegree (n : ℕ) : (rootPolynomial n).natDegree = 2 * n + 2 := by
  unfold rootPolynomial
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun i hi => Polynomial.monic_X_sub_C _)]
  simp only [Polynomial.natDegree_X_sub_C]
  simp
  omega

theorem telescoperNumerator_zero_at_nodes (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0)
    (i : Fin (n + 1) ⊕ Fin (n + 1)) : (telescoperNumerator n W).eval (rootNode n i) = 0 := by
  have hregular : ∀ k < n, rootNode n i + (k : ℚ) ≠ 0 := by
    intro k hk
    cases i with
    | inl l =>
      simp only [rootNode]
      exact ne_of_gt (by positivity)
    | inr l =>
      simp only [rootNode]
      have hkn : (k : ℚ) < (n : ℚ) := by exact_mod_cast hk
      have hl : (0 : ℚ) ≤ (l.val : ℚ) := Nat.cast_nonneg _
      exact ne_of_lt (by linarith)
  have hvalue : telescoper n W (rootNode n i) = 0 := by
    cases i with
    | inl k =>
      simpa only [rootNode, Nat.cast_add, Nat.cast_one] using
        telescoper_positive_zeros n (k.val + 1) hn W hstrong hzero (by omega) (by have := k.isLt; omega)
    | inr k =>
      exact telescoper_negative_zeros n k.val hn1 hn W hstrong hzero (by have := k.isLt; omega)
  have hrep := telescoper_actual_rational_representation n hn1 W (rootNode n i) hregular
  have hden : (polePolynomial (n - 1)).eval (rootNode n i) ^ 9 ≠ 0 :=
    pow_ne_zero _ (CoefficientMapPartialFractions.polePolynomial_eval_ne_zero (n - 1) _
      (by intro k hk; exact hregular k (by omega)))
  rw [hvalue] at hrep
  have hmult := congrArg (fun x : ℚ => x * (polePolynomial (n - 1)).eval (rootNode n i) ^ 9) hrep
  rw [div_mul_cancel₀ _ hden] at hmult
  simpa only [zero_mul] using hmult.symm

theorem all_kernel_nodes_divide_telescoperNumerator (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    rootPolynomial n ∣ telescoperNumerator n W := by
  unfold rootPolynomial
  apply Finset.prod_dvd_of_coprime
  · intro a ha b hb hab
    exact Polynomial.pairwise_coprime_X_sub_C (rootNode_injective n) hab
  · intro i hi
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def]
    exact telescoperNumerator_zero_at_nodes n hn1 hn W hstrong hzero i

theorem actual_polynomial_quotient_degree_bound (n : ℕ) (hn1 : 1 ≤ n) (hn : Even n) (W : ℚ[X])
    (hstrong : StrongProperMultiplier n W) (hzero : aggregate n W = 0) :
    ∃ H : ℚ[X], telescoperNumerator n W = rootPolynomial n * H ∧ H.natDegree ≤ 7 * n - 3 := by
  obtain ⟨H, hH⟩ := all_kernel_nodes_divide_telescoperNumerator n hn1 hn W hstrong hzero
  refine ⟨H, hH, ?_⟩
  by_cases hH0 : H = 0
  · simp [hH0]
  · have hdegree := congrArg Polynomial.natDegree hH
    rw [Polynomial.natDegree_mul (rootPolynomial_monic n).ne_zero hH0, rootPolynomial_natDegree] at hdegree
    have hbound := telescoperNumerator_natDegree_le n hn1 W
    omega

end ZetaNine.CoefficientMapTelescoper

#print axioms ZetaNine.CoefficientMapTelescoper.finite_cumulative_difference
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_difference_principal_parts
#print axioms ZetaNine.CoefficientMapTelescoper.actual_weightedR_is_difference
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_at_one_zero
#print axioms ZetaNine.CoefficientMapTelescoper.actual_weightedR_positive_zero
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_positive_zeros
#print axioms ZetaNine.CoefficientMapTelescoper.cumulativeCoefficient_reflection
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_reflection
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_negative_zeros
#print axioms ZetaNine.CoefficientMapTelescoper.telescoper_actual_rational_representation
#print axioms ZetaNine.CoefficientMapTelescoper.telescoperNumerator_natDegree_le
#print axioms ZetaNine.CoefficientMapTelescoper.rootNode_injective
#print axioms ZetaNine.CoefficientMapTelescoper.rootPolynomial_eq_explicit_products
#print axioms ZetaNine.CoefficientMapTelescoper.all_kernel_nodes_divide_telescoperNumerator
#print axioms ZetaNine.CoefficientMapTelescoper.actual_polynomial_quotient_degree_bound
