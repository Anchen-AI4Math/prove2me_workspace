import missions.zeta9.formalization.GramContent
import missions.zeta9.formalization.ProjectionDenominator
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false

open scoped BigOperators

namespace ZetaNine.CenterDenominator

open ZetaNine.GramContent

variable {ι : Type*} [Fintype ι]

/-- A primitive integral row cannot have square norm zero. Primitiveness is
expressed by an integral Bézout certificate, in arbitrary finite dimension. -/
theorem primitive_normSq_ne_zero (u : ι → ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1) : normSq u ≠ 0 := by
  classical
  intro hzero
  have hu : ∀ i, u i = 0 := by
    have hz : ∀ i ∈ Finset.univ, u i = 0 :=
      (Finset.sum_mul_self_eq_zero_iff Finset.univ u).mp
        (by simpa only [normSq, dot] using hzero)
    exact fun i => hz i (Finset.mem_univ i)
  obtain ⟨c, hc⟩ := hprimitive
  simp only [hu, mul_zero, Finset.sum_const_zero, zero_ne_one] at hc

/-- The square norm is in fact strictly positive for a primitive row. -/
theorem primitive_normSq_pos (u : ι → ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1) : 0 < normSq u := by
  have hnonneg : 0 ≤ normSq u :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)
  exact lt_of_le_of_ne hnonneg (primitive_normSq_ne_zero u hprimitive).symm

/-- The full denominator divisor of the content-adjusted rational center.
The numerator-row content coefficient `b` may have either sign and need not
be coprime to the denominator-row content coefficient `a`. Any nonzero
common divisor of all minors is allowed. -/
theorem center_denominator_divisor (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0) (hT : normSq u ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by
  have hcontent := primitive_row_gram_gcd_dvd_scaled_saturated
    u v Δ hprimitive hΔ hminor
  simpa only [mul_assoc] using
    ZetaNine.ProjectionDenominator.content_denominator_divisor
      a b (normSq u) (dot u v) (Δ * saturatedGram u v Δ) ha hT hcontent

/-- Original denominator bound (6), with the redundant norm-nonzero
assumption removed by primitiveness. This holds in every finite dimension. -/
theorem primitive_center_denominator_divisor (u v : ι → ℤ) (a b Δ : ℤ)
    (hprimitive : ∃ c : ι → ℤ, (∑ i, c i * u i) = 1)
    (ha : a ≠ 0) (hΔ : Δ ≠ 0)
    (hminor : ∀ i j, Δ ∣ u i * v j - u j * v i) :
    (normSq u).natAbs /
        Int.gcd (normSq u) (b * Δ * saturatedGram u v Δ) ∣
      (Rat.divInt (b * dot u v) (a * normSq u)).den := by
  exact center_denominator_divisor u v a b Δ hprimitive ha hΔ
    (primitive_normSq_ne_zero u hprimitive) hminor

#print axioms primitive_normSq_ne_zero
#print axioms primitive_normSq_pos
#print axioms center_denominator_divisor
#print axioms primitive_center_denominator_divisor

end ZetaNine.CenterDenominator
