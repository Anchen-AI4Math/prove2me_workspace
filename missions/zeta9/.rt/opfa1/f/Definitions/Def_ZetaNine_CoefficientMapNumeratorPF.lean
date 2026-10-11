import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_CoefficientMap
import Definitions.Def_ZetaNine_CoefficientMapJet
import Definitions.Def_ZetaNine_CoefficientMapInjectivity
import Definitions.Def_ZetaNine_CoefficientMapPartialFractions
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic





set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportData

open CoefficientMapJet CoefficientMapInjectivity















/-- Genuine formal jet for an arbitrary numerator, not an abstract array. -/
def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹

def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (numeratorClearedSeries m j A)









/- Planned universal theorem, NOT YET PROVED OR COMPILED:

weightedLocalCoefficient (n+2) j s (X^r.val) =
  extendedOldCoefficient n j s (connectionP n r) +
  extendedRemainderCoefficient n j s (connectionQ n r) -
  previousRemainderCoefficient n j s (connectionQ n r)

for n>=1, j<=n+2 and 1<=s<=9.  From this derive all nine rho
relations and the rational constant correction, then the actual row matrix
identity F_(n+2) = connectionGamma n * F_n for Even n>=2.
-/

end ZetaNine.CoefficientMapFormalTransportData





set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapNumeratorPartialFractions

open CoefficientMapInjectivity CoefficientMapPartialFractions
open CoefficientMapFormalTransportData

def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (numeratorClearedSeries m j A)

def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial m j ^ 9 *
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ))

def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (numeratorLocalCoefficient m j s A) *
      clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)

















































end ZetaNine.CoefficientMapNumeratorPartialFractions











