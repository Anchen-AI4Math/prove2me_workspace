import Definitions.Def_APSP299791_Defs5

set_option maxHeartbeats 500000
set_option autoImplicit false

namespace ThreeSumSharpTail
open Light

noncomputable def rationalRegimeCountNeed (A B : ℕ) (need : List ℕ → Need) :
    List ℕ → Need := fun ps =>
  ⟨(need (ps ++ [1])).word + (ps.getD 0 0) ^ A + (ps.getD 1 0) ^ B + ps.getD 1 0 + 100,
    (need (ps ++ [1])).cells + ps.getD 0 0 + 1, (need (ps ++ [1])).depth + 1⟩

theorem rational_getD_succ_le_prod (ps : List ℕ) (i : ℕ) :
    ps.getD i 0 + 1 ≤ (ps.map (· + 1)).prod := by
  have hpos : ∀ n ∈ ps.map (· + 1), (1 : ℕ) ≤ n := by
    intro n hn
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hn
    omega
  by_cases hi : i < ps.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.single_le_prod hpos _ (List.mem_map.mpr ⟨ps[i], List.getElem_mem hi, rfl⟩)
  · rw [List.getD_eq_default _ _ (by omega)]
    simpa using List.one_le_prod_of_one_le hpos

theorem rationalRegimeCountNeed_poly (A B : ℕ) {need : List ℕ → Need}
    (hneed : PolyNeedN need) : PolyNeedN (rationalRegimeCountNeed A B need) := by
  obtain ⟨s, k, hpoly⟩ := hneed
  refine ⟨s + k + 7, k + A + B + 1, fun ps => ?_⟩
  obtain ⟨hw, hc, hd⟩ := hpoly (ps ++ [1])
  have hN := rational_getD_succ_le_prod ps 0
  have hD := rational_getD_succ_le_prod ps 1
  have hpos : 1 ≤ (ps.map (· + 1)).prod :=
    List.one_le_prod_of_one_le (by simp)
  have hb : polyBound s k (ps ++ [1]) =
      2 ^ (s + k) * (ps.map (· + 1)).prod ^ k := by
    simp [polyBound, List.map_append, List.prod_append, mul_pow, pow_add]
    ring
  rw [hb] at hw hc hd
  generalize hqdef : (ps.map (· + 1)).prod = q at *
  let K := k + A + B + 1
  have hq : 0 < q := by omega
  have hq1 : 1 ≤ q := by omega
  have hk : q ^ k ≤ q ^ K := Nat.pow_le_pow_right hq (by dsimp [K]; omega)
  have hNpow : (ps.getD 0 0) ^ A ≤ q ^ K :=
    (Nat.pow_le_pow_left (by omega) A).trans
      (Nat.pow_le_pow_right hq (by dsimp [K]; omega))
  have hDpow : (ps.getD 1 0) ^ B ≤ q ^ K :=
    (Nat.pow_le_pow_left (by omega) B).trans
      (Nat.pow_le_pow_right hq (by dsimp [K]; omega))
  have hqpow : q ≤ q ^ K := by
    have h := Nat.pow_le_pow_right hq (show 1 ≤ K by dsimp [K]; omega)
    simpa using h
  have hpow1 : 1 ≤ q ^ K := Nat.one_le_pow _ _ hq
  have hcoef : 1 ≤ 2 ^ (s + k) := Nat.one_le_pow _ _ (by decide)
  have hbase : q ^ K ≤ 2 ^ (s + k) * q ^ K := Nat.le_mul_of_pos_left _ (by omega)
  have hW := hw.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hC := hc.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hDep := hd.trans (Nat.mul_le_mul_left (2 ^ (s + k)) hk)
  have hNp := hNpow.trans hbase
  have hDp := hDpow.trans hbase
  have hNl : ps.getD 0 0 ≤ 2 ^ (s + k) * q ^ K := (show ps.getD 0 0 ≤ q by omega).trans (hqpow.trans hbase)
  have hDl : ps.getD 1 0 ≤ 2 ^ (s + k) * q ^ K := (show ps.getD 1 0 ≤ q by omega).trans (hqpow.trans hbase)
  have hZ1 := hpow1.trans hbase
  have htarget : polyBound (s + k + 7) K ps =
      128 * (2 ^ (s + k) * q ^ K) := by
    simp only [polyBound, hqdef]
    rw [show s + k + 7 = (s + k) + 7 by omega, pow_add]
    norm_num
    ring
  change (rationalRegimeCountNeed A B need ps).word ≤ polyBound (s + k + 7) K ps ∧
    (rationalRegimeCountNeed A B need ps).cells ≤ polyBound (s + k + 7) K ps ∧
    (rationalRegimeCountNeed A B need ps).depth ≤ polyBound (s + k + 7) K ps
  rw [htarget]
  generalize hz : 2 ^ (s + k) * q ^ K = Z at *
  simp only [rationalRegimeCountNeed]
  constructor
  · omega
  · constructor <;> omega

theorem rationalRegimeCount_base_ok (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) :
    (need ([N, D, w] ++ [1])).Ok lim fr (d + 1) := by
  refine ⟨?_, ?_, hok.space, ?_⟩
  · have h := hok.word
    simp only [rationalRegimeCountNeed, Nat.cast_add] at h
    omega
  · have h := hok.cells
    simp only [rationalRegimeCountNeed] at h
    omega
  · have h := hok.depth
    simp only [rationalRegimeCountNeed] at h
    omega

theorem rationalRegimeCount_test_word (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) :
    ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤ lim.word := by
  have hn : N ^ A + D ^ B + 100 ≤
      (rationalRegimeCountNeed A B need [N, D, w]).word := by
    simp [rationalRegimeCountNeed]
    omega
  exact (show ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤
    ((rationalRegimeCountNeed A B need [N, D, w]).word : ℤ) by exact_mod_cast hn).trans hok.word

theorem rationalRegimeCount_std (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : Std lim := by
  refine ⟨hok.space, ?_⟩
  have hword := hok.word
  have hn : 100 ≤ (rationalRegimeCountNeed A B need [N,D,w]).word := by
    simp [rationalRegimeCountNeed] <;> omega
  exact (show (100 : ℤ) ≤ ((rationalRegimeCountNeed A B need [N,D,w]).word : ℤ) by exact_mod_cast hn).trans hword

theorem rationalRegimeCount_brute_space (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : fr + N + 1 ≤ lim.space := by
  have h := hok.cells
  simp only [rationalRegimeCountNeed, List.getD_cons_zero] at h
  omega

theorem rationalRegimeCount_brute_word (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : (D : ℤ) ≤ lim.word := by
  have h := hok.word
  have hn : D ≤ (rationalRegimeCountNeed A B need [N,D,w]).word := by
    simp [rationalRegimeCountNeed]
    omega
  exact (show (D : ℤ) ≤ ((rationalRegimeCountNeed A B need [N,D,w]).word : ℤ) by exact_mod_cast hn).trans h

theorem rationalRegimeCount_call_depth (A B : ℕ) {need : List ℕ → Need}
    {N D w fr d : ℕ} {lim : Limits}
    (hok : (rationalRegimeCountNeed A B need [N, D, w]).Ok lim fr d) : d + 1 ≤ lim.depth := by
  have h := hok.depth
  simp only [rationalRegimeCountNeed] at h
  omega

end ThreeSumSharpTail
#print axioms ThreeSumSharpTail.rationalRegimeCountNeed_poly
