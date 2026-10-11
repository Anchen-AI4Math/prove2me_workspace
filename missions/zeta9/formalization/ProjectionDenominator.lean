import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-! The reduced center denominator lower divisor, for arbitrary row contents.
Source: research/direction-arithmetic-next-2026-10-02.md, section 2.
-/

namespace ZetaNine.ProjectionDenominator

theorem forced_divisor (T H : ℤ) (q : ℚ) (hT : T ≠ 0)
    (hdiv : T ∣ H * (q.den : ℤ)) : T.natAbs / T.gcd H ∣ q.den := by
  have hgpos : 0 < T.gcd H := Int.gcd_pos_of_ne_zero_left H hT
  have hg0 : (T.gcd H : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (ne_of_gt hgpos)
  have hmul : T / (T.gcd H : ℤ) ∣ (H / (T.gcd H : ℤ)) * (q.den : ℤ) := by
    apply (Int.div_dvd_iff_dvd_mul (Int.gcd_dvd_left T H) hg0).2
    convert hdiv using 1
    rw [← mul_assoc, mul_comm (T.gcd H : ℤ) (H / (T.gcd H : ℤ)),
      Int.ediv_mul_cancel (Int.gcd_dvd_right T H)]
  have hd : T / (T.gcd H : ℤ) ∣ (q.den : ℤ) :=
    Int.dvd_of_dvd_mul_right_of_gcd_one hmul (Int.gcd_ediv_gcd_ediv_gcd hgpos)
  have habs := Int.natAbs_dvd_natAbs.mpr hd
  simpa only [Int.natAbs_ediv, Int.natAbs_natCast,
    Int.gcd_dvd_left, or_true, if_true, Nat.add_zero] using habs

theorem content_denominator_divisor (a b T C H : ℤ) (ha : a ≠ 0) (hT : T ≠ 0)
    (hcontent : (T.gcd C : ℤ) ∣ H) :
    T.natAbs / T.gcd (b * H) ∣ (Rat.divInt (b * C) (a * T)).den := by
  let q : ℚ := Rat.divInt (b * C) (a * T)
  have cross : q.num * (a * T) = (b * C) * (q.den : ℤ) :=
    (Rat.divInt_eq_divInt_iff (Int.natCast_ne_zero.mpr (Rat.den_nz q))
      (mul_ne_zero ha hT)).mp (Rat.num_divInt_den q)
  have hC : T ∣ b * C * (q.den : ℤ) := by
    rw [← cross]
    exact ⟨q.num * a, by ring⟩
  have hg : T ∣ b * (T.gcd C : ℤ) * (q.den : ℤ) := by
    rw [Int.gcd_eq_gcd_ab]
    have hleft : T ∣ b * (T * Int.gcdA T C) * (q.den : ℤ) :=
      ⟨b * Int.gcdA T C * (q.den : ℤ), by ring⟩
    have hright : T ∣ b * (C * Int.gcdB T C) * (q.den : ℤ) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        dvd_mul_of_dvd_left hC (Int.gcdB T C)
    convert Int.dvd_add hleft hright using 1 <;> ring
  obtain ⟨k, hk⟩ := hcontent
  apply forced_divisor T (b * H) q hT
  rw [hk]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using dvd_mul_of_dvd_left hg k

#print axioms content_denominator_divisor

end ZetaNine.ProjectionDenominator
