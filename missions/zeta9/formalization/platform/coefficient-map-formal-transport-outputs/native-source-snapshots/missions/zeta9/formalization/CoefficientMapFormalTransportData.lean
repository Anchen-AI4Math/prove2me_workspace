import missions.zeta9.formalization.CoefficientMapParameterShift
import Mathlib.Data.Matrix.Basic

/-!
UNCOMPILED DATA CANDIDATE for the genuine five-output parameter transport.
This file chooses the actual unique Connection pair and defines the real
remainder numerator and proper-numerator local jets. No PF existence,
coefficient transport or matrix identity is assumed or proved here.
The witness specification below merely reuses the existing native Connection
theorem. The new generic PF and transport obligations are in the design note.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapFormalTransportData

open CoefficientMapConnection CoefficientMapJet CoefficientMapInjectivity

def connectionPair (n : ℕ) (r : Fin 5) : ℚ[X] × ℚ[X] :=
  if hn : 1 ≤ n then
    Classical.choose (connection_five_systems_unique n hn r).exists
  else (0, 0)

def connectionP (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).1

def connectionQ (n : ℕ) (r : Fin 5) : ℚ[X] := (connectionPair n r).2

theorem connectionPair_spec (n : ℕ) (hn : 1 ≤ n) (r : Fin 5) :
    (connectionP n r).natDegree ≤ 4 ∧ (connectionQ n r).natDegree ≤ 9 ∧
      connectionD n * (connectionP n r).comp (connectionU n) +
        connectionH n (connectionQ n r) =
          (connectionTarget n r.val).comp (connectionU n) := by
  simpa only [connectionP, connectionQ, connectionPair, dif_pos hn] using
    (Classical.choose_spec (connection_five_systems_unique n hn r).exists)

/-- Rows are new monomial indices; columns are old P coefficient indices. -/
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

end ZetaNine.CoefficientMapFormalTransportData
