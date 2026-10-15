/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_APSPSource_ThreeSumApsp_Util_BinaryPrefixes
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Negative Triangle from Exact Triangle, on lists of integers

For Theorem 21(b), after [VW13, Proposition 3.4]: whether a triangle has negative weight is
expressed by O(log U) equations between binary prefixes of the shifted weights.

* The weights in `[-U, U]` are shifted to the natural numbers `x = w(a,b) + U`, `y = w(b,c) + U`,
  `v = 2U - w(a,c)`, so that a triangle is negative exactly if `x + y < v`.  The routine computes
  the prefixes `⌊z/2^ℓ⌋` (`prefQ`) of all the numbers `2x`, `2y`, `2v`, which are at most `6U`, at
  once (`negStart`, `bounds_of_mem_negStart`, `zipWith_shiftQ`, `map_shiftR`).
* For each level `ℓ` and for `e = 2` and `e = 3` the reduction makes the instance of Exact Triangle
  with the weights `⌊2x/2^ℓ⌋`, `⌊2y/2^ℓ⌋` and `e - ⌊2v/2^ℓ⌋` (`negThird`, `triOf_level`).  There is
  a negative triangle if and only if one of these instances, at a level `ℓ < L` where `3U < 2^L`,
  has a zero triangle (`hasNegativeTriangle_iff_exists_level`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The instances of the levels -/






/-- The shifted and doubled weights: `2x = 2 (w(a,b) + U)`, `2y = 2 (w(b,c) + U)`,
`2v = 2 (2U - w(a,c))`, one list after the other. -/
def negStart (U : ℕ) (AB BC AC : List ℤ) : List ℤ :=
  affL 2 (2 * U) AB ++ (affL 2 (2 * U) BC ++ affL (-2) (4 * U) AC)

/-- The third list of the instance for the level `ℓ` and the number `e`: the weights
`e - ⌊2v/2^ℓ⌋`.  A zero triangle is a triple with `⌊2v/2^ℓ⌋ = ⌊2x/2^ℓ⌋ + ⌊2y/2^ℓ⌋ + e`. -/
def negThird (U ℓ : ℕ) (e : ℤ) (AC : List ℤ) : List ℤ :=
  affL (-1) e ((affL (-2) (4 * U) AC).map (prefQ ℓ))

section Bounded

variable {n U : ℕ} {AB BC AC : List ℤ}


































































end Bounded

end ThreeSumApsp.Spec

