/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
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
import Mathlib.Data.Nat.Log
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# All pairs with a witness, by marking

The middle step of [VW18, Theorem 4.2], one of the reductions behind Theorem 21(b).
Given three `n × n` matrices `X`, `Y`, `V`, the task is to mark all pairs `(i, j)` for which some
`k` has `X[i,k] + Y[k,j] < V[i,j]` (`Witness`, `PairHit`).  The three ranges are cut into blocks of
`s` indices.

* The last block of a range is moved back so that it ends at `n`; blocks may overlap, and there are
  no padding vertices (`blockOff`, `blockCount`, `exists_block`).
* For a triple of blocks, the `s × s × s` instance `blockTri` has the weights `X[i,k]`, `Y[k,j]` and
  `-V[i,j]`; a pair that is already marked gets the weight `F = 2U + 1` instead of `-V[i,j]`
  (`maskNeg`), which is too large for a negative triangle.
* So every negative triangle that is found is an unmarked pair with a witness (`unmarked_of_neg`),
  marking it keeps the marks right (`Marks.set`) and lowers the number of unmarked pairs
  (`count_set_one`).  If the instance of a triple has no negative triangle, then every pair of the
  triple with a witness in the middle block is marked (`BlockDone`, `blockDone_of_not`), and this
  stays so when more pairs are marked (`BlockDone.set`).
* When all triples are done, the marks are the answer (`Marks.complete`).
* `tripleIdx p I K J` is the position of a triple in the order in which the triples are visited.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Blocks -/

/-- The offset of block number `I`: `I s`, or `n - s` if the block would otherwise go beyond `n`. -/
def blockOff (n s I : ℕ) : ℕ := if I * s + s ≤ n then I * s else n - s

/-- The number of blocks: `⌈n/s⌉`. -/
def blockCount (n s : ℕ) : ℕ := (n + s - 1) / s





































/-! ## The order of the triples -/

/-- The position of the triple `(I, K, J)` of numbers below `p` in the lexicographic order. -/
def tripleIdx (p I K J : ℕ) : ℕ := (I * p + K) * p + J
































/-! ## The third matrix of a block instance -/

/-- The weights of the pairs `(a, c)`: `F` for a marked pair, and `-V` otherwise. -/
def maskNeg (F : ℤ) (O V : List ℤ) : List ℤ := List.zipWith (fun o v => if o = 1 then F else -v) O V
































/-! ## Marks -/

/-- The index `k` is a witness for the pair `(i, j)`: `X[i,k] + Y[k,j] < V[i,j]`. -/
def Witness (n : ℕ) (X Y V : List ℤ) (i k j : ℕ) : Prop :=
  entry n X i k + entry n Y k j < entry n V i j

/-- The pair `(i, j)` has a witness `k < n`. -/
def PairHit (n : ℕ) (X Y V : List ℤ) (i j : ℕ) : Prop := ∃ k < n, Witness n X Y V i k j

/-- The list `O` of `n²` marks is right as far as it goes: every entry is 0 or 1, and every pair
marked 1 has a witness. -/
structure Marks (n : ℕ) (X Y V O : List ℤ) : Prop where
  len : O.length = n * n
  sound : ∀ i < n, ∀ j < n, entry n O i j = 0 ∨ (entry n O i j = 1 ∧ PairHit n X Y V i j)

/-- The triple of blocks at the offsets `oI`, `oK`, `oJ` is done: every pair of the first and the
third block that has a witness in the middle block is marked. -/
def BlockDone (n s : ℕ) (X Y V O : List ℤ) (oI oK oJ : ℕ) : Prop :=
  ∀ a < s, ∀ b < s, ∀ c < s,
    Witness n X Y V (oI + a) (oK + b) (oJ + c) → entry n O (oI + a) (oJ + c) = 1

/-- The instance for a triple of blocks. -/
def blockTri (n s : ℕ) (F : ℤ) (X Y V O : List ℤ) (oI oK oJ : ℕ) : TriangleInstance ℤ s :=
  triOf s (subMat n s oI oK X) (subMat n s oK oJ Y)
    (maskNeg F (subMat n s oI oJ O) (subMat n s oI oJ V))





















































































end ThreeSumApsp.Spec

