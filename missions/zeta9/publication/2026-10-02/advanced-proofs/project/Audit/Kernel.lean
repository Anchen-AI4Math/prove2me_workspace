import PrimeNumberTheoremAnd.MediumPNT

/-! A closed, explicit statement audit of the actual imported upstream PNT.
No assumption, local axiom or source replacement supplies this result. -/

open Filter

namespace ZetaNine.ExternalPNT

theorem checked_medium_pnt :
    ∃ c : ℝ, 0 < c ∧ Asymptotics.IsBigO atTop
      (fun x : ℝ => Chebyshev.psi x - x)
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) := by
  exact MediumPNT

#check @MediumPNT
#check @checked_medium_pnt
#print axioms MediumPNT
#print axioms checked_medium_pnt

end ZetaNine.ExternalPNT
