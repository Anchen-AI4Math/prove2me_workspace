/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.Nat.Count
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Sets of output strings as increasing lists of codes

Section 2.4.4: "we store the sets as sorted lists, so that a slice is a segment and a union of
slices is a merge".  A set `S` of output strings is stored as the strictly increasing list `codesOf
S` of its codes.  The operations of `Pruned` (Section 2.4.2) on sets become operations on lists.
None of them uses a division; a first digit is removed by a subtraction.

* The slice `S_z` is the segment `sliceList n z` of the list with first digit `z`
  (`codesOf_sliceSet`), and the list is the concatenation of its ten segments, with the first digits
  put back (`flatMap_sliceList`).
* A union is a merge, `mergeUnion` (`codesOf_union`).
* The set `S_λ` passed to the child `λ` in step (2) is `childList` (`codesOf_childSet`).
* The restriction of an array on a set to a subset is one pass, `restrictList`
  (`restrictList_spec`).

Two increasing lists are equal if they have the same elements (`List.Pairwise.eq_of_mem_iff`): the
facts on slices and on unions are proved by describing the elements of both sides.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The list of a set -/




section
variable {n : ℕ} (S : Finset (OutStr n))























end











/-! ## Slices are segments -/

/-- The numbers `c` with `a ≤ c < b` of an increasing list: skip the numbers below `a`, then take
the numbers below `b`. -/
def between (a b : ℕ) (l : List ℕ) : List ℕ :=
  (l.dropWhile fun c => c < a).takeWhile fun c => c < b

/-- The segment of an increasing list of codes with first digit `z`: the codes from `z · 10^n` on
that are below `(z+1) · 10^n`, with the first digit removed by a subtraction. -/
def sliceList (n z : ℕ) (l : List ℕ) : List ℕ :=
  (between (z * 10 ^ n) ((z + 1) * 10 ^ n) l).map fun c => c - z * 10 ^ n






















































































/-! ## Unions are merges -/

/-- The union of two strictly increasing lists, by merging; a number in both lists is kept once. -/
def mergeUnion : List ℕ → List ℕ → List ℕ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs =>
    if a < b then a :: mergeUnion as (b :: bs)
    else if b < a then b :: mergeUnion (a :: as) bs
    else a :: mergeUnion as bs














































/-- Step (2) of `Pruned` on lists: the set passed to the child with digit `t`.  The digit 9 is that
of `P₀` and of `z₀`: the child `P₀` gets the slice at `z₀`, and the child `P_ij` the union of the
slices at `z_ij` and at `z₀`. -/
def childList (n t : ℕ) (l : List ℕ) : List ℕ :=
  if t = 9 then sliceList n 9 l else mergeUnion (sliceList n t l) (sliceList n 9 l)











/-! ## Restriction to a subset is one pass -/

/-- Restriction of an array on a set to a subset, on lists: `big` is the increasing list of the set,
`vals` the list of the values in the same order, `small` the increasing list of the subset.  One
pass. -/
def restrictList : List ℕ → List ℤ → List ℕ → List ℤ
  | b :: bs, v :: vs, s :: ss =>
    if b = s then v :: restrictList bs vs ss else restrictList bs vs (s :: ss)
  | _, _, _ => []

































end ThreeSumApsp.Spec

