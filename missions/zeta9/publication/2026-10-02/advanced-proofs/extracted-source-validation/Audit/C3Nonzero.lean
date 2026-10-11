import Solutions.Sol_ZetaNine_ShortZeroCoefficient_A_ne_zero_of_even

set_option autoImplicit false
open ZetaNine.ShortZeroCoefficient

namespace ZetaNine.AdvancedAudit
theorem checked_c3_nonzero (n m : ℕ) (hn : Even n) : A n m ≠ 0 :=
  solution n m hn
#print axioms solution
#print axioms checked_c3_nonzero
end ZetaNine.AdvancedAudit
