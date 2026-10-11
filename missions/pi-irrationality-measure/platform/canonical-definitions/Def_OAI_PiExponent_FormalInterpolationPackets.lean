import Definitions.Def_OAI_PiExponent_FixedDeterminantFamily
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators
noncomputable section

namespace OAI.PiExponent.FormalInterpolation

-- FormalLogJet.liftSeries and formalJet in the pinned source.
def liftSeries (m : ℕ) : PowerSeries ℂ →+* MvPowerSeries (Fin (m + 1)) ℂ :=
  (MvPowerSeries.finSuccEquiv ℂ m).symm.toRingHom.comp
    (PowerSeries.map MvPowerSeries.C)

def formalJet {m : ℕ} (c : Fin m → ℂ) :
    MvPolynomial (Fin (m + 1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m + 1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i.succ +
      liftSeries m (PowerSeries.log ℂ)))

def WeightedPolynomial {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  {P : MvPolynomial (Fin (m + 1)) ℂ //
    ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : ℝ) ≤ H}

def packetMap {nu : ℝ} (d : DeterminantContradiction.FixedData nu) (H : ℝ)
    (P : WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (DeterminantContradiction.finiteDenominators d)) H) :
    DeterminantContradiction.Row d H → ℂ :=
  fun ρ => MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)
    (formalJet (fun i => (ρ.1.val : ℂ) *
      MatrixArithmetic.rationalCenters
        (DeterminantContradiction.finiteNumerators d)
        (DeterminantContradiction.finiteDenominators d) i) P.val)

end OAI.PiExponent.FormalInterpolation
