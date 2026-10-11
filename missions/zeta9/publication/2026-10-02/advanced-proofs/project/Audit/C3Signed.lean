import Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_even_signed_lower

set_option autoImplicit false
open ZetaNine.ShortZeroCoefficient

namespace ZetaNine.AdvancedAudit
theorem checked_c3_signed_lower (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
      ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m :=
  solution d m
#print axioms solution
#print axioms checked_c3_signed_lower
end ZetaNine.AdvancedAudit
