import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace ZetaNine.NPFDataValueAliases
open CoefficientMapConnection CoefficientMapJet CoefficientMapInjectivity
def connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then
    Classical.choose (connection_five_systems_unique n hn r).exists
  else (0, 0)


def connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).1


def connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).2


def connectionGamma (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun r l => (connectionP n r).coeff l.val

/-- True cancellation numerator for Q(t), with denominator
    ((t-1) polePolynomial_n(t))^9.  The positive roots are 2,...,n+1. -/

def remainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
    (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))) *
    q.comp (connectionV n)


def shiftedRemainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (remainderNumerator n q).comp (X + 1)

/-- Genuine formal jet for an arbitrary numerator, not an abstract array. -/

def numeratorClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  ((A.comp (shiftedVariable j) : ℚ[X]) : PowerSeries ℚ) *
    ((shiftedClearedDenominator m j : PowerSeries ℚ) ^ 9)⁻¹


def numeratorLocalCoefficient (m j s : ℕ) (A : ℚ[X]) : ℚ :=
  PowerSeries.coeff (9 - s) (numeratorClearedSeries m j A)


def remainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  numeratorLocalCoefficient (n + 1) j s (shiftedRemainderNumerator n q)


def extendedOldCoefficient (n j s : ℕ) (P : ℚ[X]) : ℚ :=
  if 1 ≤ j ∧ j ≤ n + 1 then weightedLocalCoefficient n (j - 1) s P else 0


def extendedRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j ≤ n + 1 then remainderCoefficient n j s q else 0


def previousRemainderCoefficient (n j s : ℕ) (q : ℚ[X]) : ℚ :=
  if j = 0 then 0 else extendedRemainderCoefficient n (j - 1) s q

/- Planned universal theorem, NOT YET PROVED OR COMPILED:

weightedLocalCoefficient (n+2) j s (X^r.val) =
  extendedOldCoefficient n j s (connectionP n r) +
  extendedRemainderCoefficient n j s (connectionQ n r) -
  previousRemainderCoefficient n j s (connectionQ n r)

for n>=1, j<=n+2 and 1<=s<=9.  From this derive all nine rho
relations and the rational constant correction, then the actual row matrix
identity F_(n+2) = connectionGamma n * F_n for Even n>=2.
-/


end ZetaNine.NPFDataValueAliases
namespace ZetaNine.NPFValueAliases
open CoefficientMapInjectivity CoefficientMapPartialFractions CoefficientMapFormalTransportData
def numeratorLocalTruncation (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  PowerSeries.trunc 9 (numeratorClearedSeries m j A)


def numeratorPartialBlock (m j : ℕ) (A : ℚ[X]) : ℚ[X] :=
  clearedPolePolynomial m j ^ 9 *
    (numeratorLocalTruncation m j A).comp (X + C (j : ℚ))


def numeratorPartialNumerator (m : ℕ) (A : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range (m + 1), ∑ s ∈ Icc 1 9,
    C (numeratorLocalCoefficient m j s A) *
      clearedPolePolynomial m j ^ 9 * (X + C (j : ℚ)) ^ (9 - s)


def numeratorCandidateClearedSeries (m j : ℕ) (A : ℚ[X]) : PowerSeries ℚ :=
  numeratorClearedSeries m j (numeratorPartialNumerator m A)


end ZetaNine.NPFValueAliases
theorem value_Data_connectionPair : ZetaNine.NPFDataValueAliases.connectionPair = ZetaNine.CoefficientMapFormalTransportData.connectionPair := rfl
theorem value_Data_connectionP : ZetaNine.NPFDataValueAliases.connectionP = ZetaNine.CoefficientMapFormalTransportData.connectionP := rfl
theorem value_Data_connectionQ : ZetaNine.NPFDataValueAliases.connectionQ = ZetaNine.CoefficientMapFormalTransportData.connectionQ := rfl
theorem value_Data_connectionGamma : ZetaNine.NPFDataValueAliases.connectionGamma = ZetaNine.CoefficientMapFormalTransportData.connectionGamma := rfl
theorem value_Data_remainderNumerator : ZetaNine.NPFDataValueAliases.remainderNumerator = ZetaNine.CoefficientMapFormalTransportData.remainderNumerator := rfl
theorem value_Data_shiftedRemainderNumerator : ZetaNine.NPFDataValueAliases.shiftedRemainderNumerator = ZetaNine.CoefficientMapFormalTransportData.shiftedRemainderNumerator := rfl
theorem value_Data_numeratorClearedSeries : ZetaNine.NPFDataValueAliases.numeratorClearedSeries = ZetaNine.CoefficientMapFormalTransportData.numeratorClearedSeries := rfl
theorem value_Data_numeratorLocalCoefficient : ZetaNine.NPFDataValueAliases.numeratorLocalCoefficient = ZetaNine.CoefficientMapFormalTransportData.numeratorLocalCoefficient := rfl
theorem value_Data_remainderCoefficient : ZetaNine.NPFDataValueAliases.remainderCoefficient = ZetaNine.CoefficientMapFormalTransportData.remainderCoefficient := rfl
theorem value_Data_extendedOldCoefficient : ZetaNine.NPFDataValueAliases.extendedOldCoefficient = ZetaNine.CoefficientMapFormalTransportData.extendedOldCoefficient := rfl
theorem value_Data_extendedRemainderCoefficient : ZetaNine.NPFDataValueAliases.extendedRemainderCoefficient = ZetaNine.CoefficientMapFormalTransportData.extendedRemainderCoefficient := rfl
theorem value_Data_previousRemainderCoefficient : ZetaNine.NPFDataValueAliases.previousRemainderCoefficient = ZetaNine.CoefficientMapFormalTransportData.previousRemainderCoefficient := rfl
theorem value_PF_numeratorLocalTruncation : ZetaNine.NPFValueAliases.numeratorLocalTruncation = ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorLocalTruncation := rfl
theorem value_PF_numeratorPartialBlock : ZetaNine.NPFValueAliases.numeratorPartialBlock = ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialBlock := rfl
theorem value_PF_numeratorPartialNumerator : ZetaNine.NPFValueAliases.numeratorPartialNumerator = ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorPartialNumerator := rfl
theorem value_PF_numeratorCandidateClearedSeries : ZetaNine.NPFValueAliases.numeratorCandidateClearedSeries = ZetaNine.CoefficientMapNumeratorPartialFractions.numeratorCandidateClearedSeries := rfl
