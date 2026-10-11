import missions.zeta9.formalization.CoefficientMapNumeratorPartialFractions
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial
namespace NumeratorPFIndependentDataValues
open ZetaNine.CoefficientMapConnection ZetaNine.CoefficientMapJet ZetaNine.CoefficientMapInjectivity
def connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then
    Classical.choose (connection_five_systems_unique n hn r).exists
  else (0, 0)

def connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).1

def connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).2

def connectionGamma (n : ℕ) : Matrix (Fin 5) (Fin 5) ℚ :=
  fun r l => (connectionP n r).coeff l.val

def remainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 2))) *
    (∏ i ∈ range n, (X + C ((n : ℚ) + (i : ℚ) + 1))) *
    q.comp (connectionV n)

def shiftedRemainderNumerator (n : ℕ) (q : ℚ[X]) : ℚ[X] :=
  (remainderNumerator n q).comp (X + 1)

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
end NumeratorPFIndependentDataValues
namespace NumeratorPFIndependentValues
open ZetaNine.CoefficientMapFormalTransportData ZetaNine.CoefficientMapInjectivity
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
end NumeratorPFIndependentValues
