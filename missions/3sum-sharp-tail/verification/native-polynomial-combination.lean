import Definitions.Def_APSP299791_Defs5

namespace Light

theorem sharpTail_polyNeedN_snoc_one {need : List ℕ → Need} (h : PolyNeedN need) :
    PolyNeedN (fun ps => need (ps ++ [1])) := by
  obtain ⟨s, k, h⟩ := h
  refine ⟨s + k, k, fun ps => ?_⟩
  have hb : polyBound s k (ps ++ [1]) = polyBound (s + k) k ps := by
    simp [polyBound, List.map_append, List.prod_append, mul_pow, pow_add]
    ring
  have hh := h (ps ++ [1])
  rw [hb] at hh
  exact hh

theorem sharpTail_polyNeed_bySize (n₀ : ℕ) {r₁ r₂ : ℕ → ℕ → Need}
    (h₁ : PolyNeed r₁) (h₂ : PolyNeed r₂) : PolyNeed (Sec3.bySizeNeed n₀ r₁ r₂) := by
  obtain ⟨s₁, k₁, h₁⟩ := h₁
  obtain ⟨s₂, k₂, h₂⟩ := h₂
  refine ⟨s₁ + s₂ + n₀ + 2, k₁ + k₂, fun n U => ?_⟩
  let q := (n + 1) * (U + 1)
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by omega
  have hpow1 : q ^ k₁ ≤ q ^ (k₁ + k₂) := Nat.pow_le_pow_right hq (by omega)
  have hpow2 : q ^ k₂ ≤ q ^ (k₁ + k₂) := Nat.pow_le_pow_right hq (by omega)
  have hpow0 : 1 ≤ q ^ (k₁ + k₂) := Nat.one_le_pow _ _ hq
  have hs₁ : 2 ^ s₁ ≤ 2 ^ (s₁ + s₂ + n₀) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hs₂ : 2 ^ s₂ ≤ 2 ^ (s₁ + s₂ + n₀) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hsc : n₀ + 1 ≤ 2 ^ (s₁ + s₂ + n₀) :=
    (show n₀ + 1 ≤ 2 ^ n₀ by have h : n₀ < 2 ^ n₀ := Nat.lt_two_pow_self; omega).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  have hbound₁ : polyBound s₁ k₁ [n, U] ≤
      2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) := by
    simpa [polyBound, q] using Nat.mul_le_mul hs₁ hpow1
  have hbound₂ : polyBound s₂ k₂ [n, U] ≤
      2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) := by
    simpa [polyBound, q] using Nat.mul_le_mul hs₂ hpow2
  have hboundC : n₀ + 1 ≤ 2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂) :=
    hsc.trans (Nat.le_mul_of_pos_right _ (by omega))
  obtain ⟨hw₁, hc₁, hd₁⟩ := h₁ n U
  obtain ⟨hw₂, hc₂, hd₂⟩ := h₂ n U
  have htarget : polyBound (s₁ + s₂ + n₀ + 2) (k₁ + k₂) [n, U] =
      4 * (2 ^ (s₁ + s₂ + n₀) * q ^ (k₁ + k₂)) := by
    simp only [polyBound, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [pow_add]
    dsimp [q]
    ring
  simp only [Sec3.bySizeNeed, htarget]
  constructor
  · omega
  · constructor <;> omega

end Light

#print axioms Light.sharpTail_polyNeedN_snoc_one
#print axioms Light.sharpTail_polyNeed_bySize
