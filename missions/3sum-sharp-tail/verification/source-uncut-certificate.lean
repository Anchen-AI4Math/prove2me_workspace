import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 1000
open scoped BigOperators

namespace ThreeSumSharpTail.Certificate

/-- The rational atanh partial sum used by the manuscript's certificates. -/
noncomputable def logSeries (n : ℕ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, z ^ (2 * i + 1) / (2 * i + 1)

lemma log_bounds_of_atanh {y z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1)
    (hy : (1 + z) / (1 - z) = y) (n : ℕ) :
    2 * logSeries n z ≤ Real.log y ∧
      Real.log y ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
  have hlo := Real.sum_range_le_log_div hz0 hz1 n
  have hhi := Real.log_div_le_sum_range_add hz0 hz1 n
  constructor
  · calc
      2 * logSeries n z ≤ Real.log ((1 + z) / (1 - z)) := by
        simpa [logSeries, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using
          (mul_le_mul_of_nonneg_left hlo (by norm_num : 0 ≤ (2 : ℝ)))
      _ = Real.log y := by rw [hy]
  · calc
      Real.log y = Real.log ((1 + z) / (1 - z)) := by rw [hy]
      _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
        have hm := mul_le_mul_of_nonneg_left hhi (by norm_num : 0 ≤ (2 : ℝ))
        calc
          Real.log ((1 + z) / (1 - z)) =
              2 * (1 / 2 * Real.log ((1 + z) / (1 - z))) := by ring
          _ ≤ 2 * (logSeries n z + z ^ (2 * n + 1) / (1 - z ^ 2)) := by
            simpa [logSeries] using hm

lemma log_two_certificate :
    (693147180559945 / 10^15 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ 693147180559946 / 10^15 := by
  have h := log_bounds_of_atanh (y := 2) (z := (1 : ℝ) / 3)
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · have hs : (693147180559945 / 10^15 : ℝ) ≤
        2 * logSeries 16 ((1 : ℝ) / 3) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 16 ((1 : ℝ) / 3) +
        ((1 : ℝ) / 3) ^ (2 * 16 + 1) / (1 - ((1 : ℝ) / 3) ^ 2)) ≤
          693147180559946 / 10^15 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_seven_fourths_certificate :
    (559615787935422686 / 10^18 : ℝ) ≤ Real.log (7 / 4) ∧
      Real.log (7 / 4) ≤ 559615787935422687 / 10^18 := by
  have h := log_bounds_of_atanh (y := (7 : ℝ) / 4) (z := (3 : ℝ) / 11)
    (by norm_num) (by norm_num) (by norm_num) 16
  constructor
  · have hs : (559615787935422686 / 10^18 : ℝ) ≤
        2 * logSeries 16 ((3 : ℝ) / 11) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 16 ((3 : ℝ) / 11) +
        ((3 : ℝ) / 11) ^ (2 * 16 + 1) / (1 - ((3 : ℝ) / 11) ^ 2)) ≤
          559615787935422687 / 10^18 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_seven_over_log_two_lt : Real.log 7 / Real.log 2 < (281 : ℝ) / 100 := by
  have hpow : 7 ^ 100 < (2 : ℕ) ^ 281 := by decide
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ 100)
    (by exact_mod_cast hpow : (7 : ℝ) ^ 100 < (2 : ℝ) ^ 281)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hden : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : Real.log 7 < (281 : ℝ) / 100 * Real.log 2 := by
    calc
      Real.log 7 < (281 * Real.log 2) / 100 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 (by norm_num at hlog; linarith)
      _ = (281 : ℝ) / 100 * Real.log 2 := by ring
  exact (div_lt_iff₀ hden).2 hscaled

lemma log_5_4_cert :
    (223143551 / 10^9 : ℝ) ≤ Real.log (5 / 4) ∧ Real.log (5 / 4) ≤ 223143552 / 10^9 := by
  have h := log_bounds_of_atanh (y := (5 : ℝ) / 4) (z := (1 : ℝ) / 9)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (223143551 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 9) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 9) + ((1 : ℝ) / 9) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 9) ^ 2)) ≤ 223143552 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_3_2_cert :
    (405465108 / 10^9 : ℝ) ≤ Real.log (3 / 2) ∧ Real.log (3 / 2) ≤ 405465109 / 10^9 := by
  have h := log_bounds_of_atanh (y := (3 : ℝ) / 2) (z := (1 : ℝ) / 5)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (405465108 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 5) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 5) + ((1 : ℝ) / 5) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 5) ^ 2)) ≤ 405465109 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_9_8_cert :
    (117783035 / 10^9 : ℝ) ≤ Real.log (9 / 8) ∧ Real.log (9 / 8) ≤ 117783036 / 10^9 := by
  have h := log_bounds_of_atanh (y := (9 : ℝ) / 8) (z := (1 : ℝ) / 17)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (117783035 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1 : ℝ) / 17) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1 : ℝ) / 17) + ((1 : ℝ) / 17) ^ (2 * 12 + 1) / (1 - ((1 : ℝ) / 17) ^ 2)) ≤ 117783036 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_21_16_cert :
    (271933715 / 10^9 : ℝ) ≤ Real.log (21 / 16) ∧ Real.log (21 / 16) ≤ 271933716 / 10^9 := by
  have h := log_bounds_of_atanh (y := (21 : ℝ) / 16) (z := (5 : ℝ) / 37)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (271933715 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((5 : ℝ) / 37) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((5 : ℝ) / 37) + ((5 : ℝ) / 37) ^ (2 * 12 + 1) / (1 - ((5 : ℝ) / 37) ^ 2)) ≤ 271933716 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_32_21_cert :
    (421213465 / 10^9 : ℝ) ≤ Real.log (32 / 21) ∧ Real.log (32 / 21) ≤ 421213466 / 10^9 := by
  have h := log_bounds_of_atanh (y := (32 : ℝ) / 21) (z := (11 : ℝ) / 53)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (421213465 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((11 : ℝ) / 53) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((11 : ℝ) / 53) + ((11 : ℝ) / 53) ^ (2 * 12 + 1) / (1 - ((11 : ℝ) / 53) ^ 2)) ≤ 421213466 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_40_21_cert :
    (644357016 / 10^9 : ℝ) ≤ Real.log (40 / 21) ∧ Real.log (40 / 21) ≤ 644357017 / 10^9 := by
  have h := log_bounds_of_atanh (y := (40 : ℝ) / 21) (z := (19 : ℝ) / 61)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (644357016 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((19 : ℝ) / 61) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((19 : ℝ) / 61) + ((19 : ℝ) / 61) ^ (2 * 12 + 1) / (1 - ((19 : ℝ) / 61) ^ 2)) ≤ 644357017 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_88798_65625_cert :
    (302407406 / 10^9 : ℝ) ≤ Real.log (88798 / 65625) ∧ Real.log (88798 / 65625) ≤ 302407407 / 10^9 := by
  have h := log_bounds_of_atanh (y := (88798 : ℝ) / 65625) (z := (23173 : ℝ) / 154423)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (302407406 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((23173 : ℝ) / 154423) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((23173 : ℝ) / 154423) + ((23173 : ℝ) / 154423) ^ (2 * 12 + 1) / (1 - ((23173 : ℝ) / 154423) ^ 2)) ≤ 302407407 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_1005601_525000_cert :
    (649942389 / 10^9 : ℝ) ≤ Real.log (1005601 / 525000) ∧ Real.log (1005601 / 525000) ≤ 649942390 / 10^9 := by
  have h := log_bounds_of_atanh (y := (1005601 : ℝ) / 525000) (z := (480601 : ℝ) / 1530601)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (649942389 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((480601 : ℝ) / 1530601) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((480601 : ℝ) / 1530601) + ((480601 : ℝ) / 1530601) ^ (2 * 12 + 1) / (1 - ((480601 : ℝ) / 1530601) ^ 2)) ≤ 649942390 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_5601_3125_cert :
    (583510870 / 10^9 : ℝ) ≤ Real.log (5601 / 3125) ∧ Real.log (5601 / 3125) ≤ 583510871 / 10^9 := by
  have h := log_bounds_of_atanh (y := (5601 : ℝ) / 3125) (z := (1238 : ℝ) / 4363)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (583510870 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((1238 : ℝ) / 4363) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((1238 : ℝ) / 4363) + ((1238 : ℝ) / 4363) ^ (2 * 12 + 1) / (1 - ((1238 : ℝ) / 4363) ^ 2)) ≤ 583510871 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_44399_25000_cert :
    (574341121 / 10^9 : ℝ) ≤ Real.log (44399 / 25000) ∧ Real.log (44399 / 25000) ≤ 574341122 / 10^9 := by
  have h := log_bounds_of_atanh (y := (44399 : ℝ) / 25000) (z := (19399 : ℝ) / 69399)
    (by norm_num) (by norm_num) (by norm_num) 12
  constructor
  · have hs : (574341121 / 10^9 : ℝ) ≤ 2 * logSeries 12 ((19399 : ℝ) / 69399) := by norm_num [logSeries]
    exact hs.trans h.1
  · have hs : 2 * (logSeries 12 ((19399 : ℝ) / 69399) + ((19399 : ℝ) / 69399) ^ (2 * 12 + 1) / (1 - ((19399 : ℝ) / 69399) ^ 2)) ≤ 574341122 / 10^9 := by norm_num [logSeries]
    exact h.2.trans hs

lemma log_scale_up (x y : ℝ) (k : ℕ) (hx : 0 < y)
    (hxy : x = y * (2 : ℝ) ^ k) : Real.log x = Real.log y + k * Real.log 2 := by
  rw [hxy, Real.log_mul (ne_of_gt hx) (by positivity), Real.log_pow]

lemma log_scale_down (x y : ℝ) (k : ℕ) (hx : 0 < x)
    (hxy : y = x * (2 : ℝ) ^ k) : Real.log x = Real.log y - k * Real.log 2 := by
  have h := log_scale_up y x k hx hxy
  linarith

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have hpow : (4 : ℝ) = 2 * 2 := by norm_num
  rw [hpow]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

end ThreeSumSharpTail.Certificate

theorem solution :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625 := by
  have l2 := ThreeSumSharpTail.Certificate.log_two_certificate
  have l7q := ThreeSumSharpTail.Certificate.log_seven_fourths_certificate
  have l5q := ThreeSumSharpTail.Certificate.log_5_4_cert
  have l3q := ThreeSumSharpTail.Certificate.log_3_2_cert
  have l9q := ThreeSumSharpTail.Certificate.log_9_8_cert
  have l21q := ThreeSumSharpTail.Certificate.log_21_16_cert
  have l32q := ThreeSumSharpTail.Certificate.log_32_21_cert
  have l40q := ThreeSumSharpTail.Certificate.log_40_21_cert
  have luq := ThreeSumSharpTail.Certificate.log_88798_65625_cert
  have lucq := ThreeSumSharpTail.Certificate.log_1005601_525000_cert
  have l5601q := ThreeSumSharpTail.Certificate.log_5601_3125_cert
  have l44399q := ThreeSumSharpTail.Certificate.log_44399_25000_cert
  have l7 : (1945910149 / 10^9 : ℝ) ≤ Real.log 7 ∧ Real.log 7 ≤ 1945910150 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_up 7 (7 / 4) 2 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l7q.1, l7q.2]
  have l10 : (2302585092 / 10^9 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2302585094 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_up 10 (5 / 4) 3 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l5q.1, l5q.2]
  have l3 : (1098612288 / 10^9 : ℝ) ≤ Real.log 3 ∧ Real.log 3 ≤ 1098612290 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_up 3 (3 / 2) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l3q.1, l3q.2]
  have l9 : (2197224575 / 10^9 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 2197224580 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_up 9 (9 / 8) 3 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l9q.1, l9q.2]
  have l21 : (3044522437 / 10^9 : ℝ) ≤ Real.log 21 ∧ Real.log 21 ≤ 3044522439 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_up 21 (21 / 16) 4 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l21q.1, l21q.2]
  have linv21 : (-3044522438 / 10^9 : ℝ) ≤ Real.log (1 / 21) ∧ Real.log (1 / 21) ≤ -3044522436 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (1 / 21) (32 / 21) 5 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l32q.1, l32q.2]
  have l20_21 : (-48790165 / 10^9 : ℝ) ≤ Real.log (20 / 21) ∧ Real.log (20 / 21) ≤ -48790163 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (20 / 21) (40 / 21) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l40q.1, l40q.2]
  have lu : (-3163328497 / 10^9 : ℝ) ≤ Real.log (44399 / 1050000) ∧ Real.log (44399 / 1050000) ≤ -3163328495 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (44399 / 1050000) (88798 / 65625) 5 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, luq.1, luq.2]
  have luc : (-43204792 / 10^9 : ℝ) ≤ Real.log (1005601 / 1050000) ∧ Real.log (1005601 / 1050000) ≤ -43204790 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (1005601 / 1050000) (1005601 / 525000) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, lucq.1, lucq.2]
  have lt : (-2189077853 / 10^9 : ℝ) ≤ Real.log (5601 / 50000) ∧ Real.log (5601 / 50000) ≤ -2189077851 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (5601 / 50000) (5601 / 3125) 4 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l5601q.1, l5601q.2]
  have ltc : (-118806060 / 10^9 : ℝ) ≤ Real.log (44399 / 50000) ∧ Real.log (44399 / 50000) ≤ -118806057 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_scale_down (44399 / 50000) (44399 / 25000) 1 (by norm_num) (by norm_num)]
    constructor <;> nlinarith [l2.1, l2.2, l44399q.1, l44399q.2]
  have hE : (19144408 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (1 / 21) ∧
      ThreeSumSharpTail.entropy (1 / 21) ≤ 19144409 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> nlinarith [linv21.1, linv21.2, l20_21.1, l20_21.2]
  have hU : (17513847 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (44399 / 1050000) ∧
      ThreeSumSharpTail.entropy (44399 / 1050000) ≤ 17513849 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> nlinarith [lu.1, lu.2, luc.1, luc.2]
  have hT : (35071790 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (5601 / 50000) ∧
      ThreeSumSharpTail.entropy (5601 / 50000) ≤ 35071791 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> linarith [lt.1, lt.2, ltc.1, ltc.2]
  have l4 : (1386294361 / 10^9 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ 1386294362 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_four_eq]
    constructor <;> linarith only [l2.1, l2.2]
  have hgamma : (69454 / 10^6 : ℝ) ≤ ThreeSumSharpTail.sharpSaving 21 (5601 / 50000) ∧
      ThreeSumSharpTail.sharpSaving 21 (5601 / 50000) ≤ 69456 / 10^6 := by
    have harg : (1 - (5601 : ℝ) / 50000) / 21 = (44399 : ℝ) / 1050000 := by norm_num
    have h4pos : 0 < Real.log 4 := by linarith only [l4.1]
    have hnlo : (69454 / 10^6 : ℝ) * Real.log 4 ≤
        21 * ThreeSumSharpTail.entropy (1 / 21) - 21 * ThreeSumSharpTail.entropy (44399 / 1050000) -
          (5601 : ℝ) / 50000 * Real.log 9 := by linarith only [hE.1, hU.2, l9.2, l4.2]
    have hnhi : 21 * ThreeSumSharpTail.entropy (1 / 21) - 21 * ThreeSumSharpTail.entropy (44399 / 1050000) -
          (5601 : ℝ) / 50000 * Real.log 9 ≤ (69456 / 10^6 : ℝ) * Real.log 4 := by
      linarith only [hE.2, hU.1, l9.1, l4.1]
    unfold ThreeSumSharpTail.sharpSaving
    rw [harg]
    constructor
    · exact (le_div_iff₀ h4pos).2 hnlo
    · exact (div_le_iff₀ h4pos).2 hnhi
  have hquery : ThreeSumSharpTail.queryExponent (5601 / 50000) ≤ (43054 / 100000 : ℝ) := by
    unfold ThreeSumSharpTail.queryExponent
    have hnum : ThreeSumSharpTail.entropy (5601 / 50000) + (5601 / 50000) * Real.log 9 ≤
        (43054 / 100000 : ℝ) * Real.log 4 := by
      linarith only [hT.2, l9.2, l4.1]
    exact (div_le_iff₀ (by linarith only [l4.1])).2 hnum
  have henc : ThreeSumSharpTail.encodingExponent 21 ≤ (17581 / 1000 : ℝ) := by
    unfold ThreeSumSharpTail.encodingExponent
    have hnum : 21 * Real.log 10 - 21 * ThreeSumSharpTail.entropy (1 / 21) / 2 - (21 - 1) * Real.log 3 ≤
        (17581 / 1000 : ℝ) * Real.log 4 := by
      norm_num
      linarith only [hE.1, l10.2, l3.1, l4.1]
    exact (div_le_iff₀ (by linarith only [l4.1])).2 hnum
  have hLogRatio := ThreeSumSharpTail.Certificate.log_seven_over_log_two_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num at henc hgamma ⊢
    linarith only [henc, hgamma.2]
  · norm_num at hgamma ⊢
    linarith only [hgamma.1]
  · norm_num at hquery ⊢
    linarith only [hquery]
  · norm_num at hLogRatio ⊢
    linarith only [hLogRatio]
  · norm_num
  · norm_num
  · norm_num
