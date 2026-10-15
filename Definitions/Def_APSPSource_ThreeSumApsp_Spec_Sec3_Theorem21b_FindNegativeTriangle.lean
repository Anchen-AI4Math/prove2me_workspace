/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Finding a negative triangle by halving

[VW18, Lemma 4.1], one of the reductions behind Theorem 21(b): an algorithm that
decides whether a graph has a negative triangle also finds one.  The search keeps three offsets and
a side length `h` such that the `h × h × h` sub-instance at these offsets has a negative triangle
(`NegAt`), and replaces `h` by `⌈h/2⌉`.

* The sub-instance is an instance of its own, made of three blocks of the matrices (`subMat`,
  `hasNegativeTriangle_subMat_iff`), so the decision algorithm can be asked about it.
* Each of the three ranges `[o, o + h)` is covered by its two halves `[o, o + ⌈h/2⌉)` and
  `[o + h - ⌈h/2⌉, o + h)`, which overlap in one place if `h` is odd.  So one of the eight triples
  of halves (`octants`) has a negative triangle (`NegAt.split`).
* At side length 1 the sub-instance is the triangle (`NegAt.triangle`).
* The side lengths `⌈n/2⌉, ⌈⌈n/2⌉/2⌉, …, 1` that the search goes through (`halvingChain`) add up to
  at most `2n` (`sum_halvingChain_le`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Sub-instances -/

/-- The sub-instance on the vertices `a0 + a`, `b0 + b`, `c0 + c` with `a, b, c < h` has a negative
triangle. -/
def NegAt (n : ℕ) (AB BC AC : List ℤ) (a0 b0 c0 h : ℕ) : Prop :=
  ∃ a < h, ∃ b < h, ∃ c < h,
    entry n AB (a0 + a) (b0 + b) + entry n BC (b0 + b) (c0 + c) +
      entry n AC (a0 + a) (c0 + c) < 0
































/-! ## The step of the search -/

/-- The eight triples of halves: 0 stands for the lower half of a range and 1 for the upper
half. -/
def octants : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 0), (0, 0, 1), (0, 1, 0), (0, 1, 1), (1, 0, 0), (1, 0, 1), (1, 1, 0), (1, 1, 1)]






























/-! ## The chain of side lengths -/

/-- The side lengths after `n`: `⌈n/2⌉`, then `⌈⌈n/2⌉/2⌉`, and so on down to 1.  Empty for `n ≤ 1`.
-/
def halvingChain (n : ℕ) : List ℕ :=
  if 2 ≤ n then (n + 1) / 2 :: halvingChain ((n + 1) / 2) else []
termination_by n
decreasing_by omega









































end ThreeSumApsp.Spec

