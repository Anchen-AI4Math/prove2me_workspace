/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Hashing modulo a prime (proof of Theorem 17), on numbers and lists

The reduction of Theorem 17 hashes the weights modulo a prime `p` of the window `√D/2 ≤ p < √D` and
selects the prime with the fewest triples `(a,b,c)` with `S(a,b,c) ≡ 0 (mod p)`, where
`S(a,b,c) = w(a,b) + w(b,c) + w(a,c)`.  This file has the parts of this step that a program
computes:

* the residue of a weight as a natural number below `p` (`resid`, `residList`);
* the entries of the matrices `P` and `Q` of the proof of Theorem 17 as unit vectors (`cycVec_matP`,
  `cycVec_matQ`), and the count of the triples, read off the vectors of `PQ` (`countZeroMod_eq`);
* the primes of the window by comparisons of integers (`primesList`, `primesInRange_eq`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Residues -/

/-- The residue of `w` modulo `p` in `{0, …, p − 1}`. -/
def resid (p : ℕ) (w : ℤ) : ℕ := (w % (p : ℤ)).toNat
























/-- The residues of a list. -/
def residList (p : ℕ) (l : List ℤ) : List ℕ := l.map (resid p)







/-- The table `p, 2p, 4p, …, 2^len p`. -/
def dblList (p len : ℕ) : List ℤ := (List.range (len + 1)).map fun j : ℕ => ((p * 2 ^ j : ℕ) : ℤ)

/-- The number of binary digits of `U`: the least `len` with `U < 2^len`. -/
def bitLen (U : ℕ) : ℕ := Nat.size U

/-! ## The count of the proof of Theorem 17 -/






















/-! ## The primes of the window -/

/-- The primes `p` with `√D/2 ≤ p < √D`, by integer comparisons: `D ≤ 4p²` and `p² < D`. -/
def primesList (D : ℕ) : List ℕ :=
  (List.range D).filter fun p => p.Prime ∧ D ≤ 4 * p ^ 2 ∧ p ^ 2 < D































end ThreeSumApsp.Spec

