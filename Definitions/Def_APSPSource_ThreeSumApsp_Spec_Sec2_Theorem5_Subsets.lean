/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The subsets of size `m` of `{1, …, L}`, enumerated

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  A subset is a *mask*: the list of `L` truth values saying
which levels belong to it, level 1 first (`maskSet`, `maskOf`).  The subsets of size `m` are
enumerated with those containing level 1 first, and so on recursively: `unrank L m r` is number `r`
in this order.

* The masks `unrank L m r` with `r < (L choose m)` have length `L` and `m` entries `true`, and they
  are distinct, because `rank` recovers `r` (`length_unrank`, `count_unrank`, `rank_unrank`).  So
  their sets of levels are distinct subsets of size `m` (`card_maskSet_unrank`,
  `eq_of_maskSet_unrank_eq`).
* A program lists them in a table without arithmetic, each mask from the one before it: the first
  mask is `true^m false^{L-m}` (`unrank_zero`), and two consecutive masks are
  `pre true false false^a true^b` and `pre false true true^b false^a` (`unrank_succ_shape`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The enumeration -/

/-- The mask number `r` (counted from 0) among the masks of length `L` with `m` entries `true`. -/
def unrank : ℕ → ℕ → ℕ → List Bool
  | 0, _, _ => []
  | L + 1, 0, _ => false :: unrank L 0 0
  | L + 1, m + 1, r =>
    if r < L.choose m then true :: unrank L m r else false :: unrank L (m + 1) (r - L.choose m)

/-- The position of a mask in the enumeration.  A mask that begins with `false` comes after all the
masks with the same number of entries `true` that begin with `true`; if the rest `l` of the mask has
`k > 0` entries `true`, there are `(|l| choose k - 1)` of them. -/
 def rank : List Bool → ℕ
  | [] => 0
  | true :: l => rank l
  | false :: l => (if l.count true = 0 then 0 else l.length.choose (l.count true - 1)) + rank l

/-- A mask of the enumeration has length `L`. -/
@[simp] theorem length_unrank (L m r : ℕ) : (unrank L m r).length = L := by
  fun_induction unrank L m r <;> simp [*]

/-- A mask of the enumeration has `m` entries `true`. -/
theorem count_unrank {L m r : ℕ} (hr : r < L.choose m) : (unrank L m r).count true = m := by
  -- Along the recursion of `unrank`; by Pascal's rule the number passed on is again in range.
  fun_induction unrank L m r <;> grind [Nat.choose_succ_succ']








/-- `rank` undoes `unrank`. -/
 theorem rank_unrank {L m r : ℕ} (hr : r < L.choose m) : rank (unrank L m r) = r := by
  fun_induction unrank L m r with
  | case1 m r =>
    -- No levels: the only mask is the empty one, and `r = 0`.
    cases m <;> simp_all [rank]
  | case2 L r ih =>
    -- The empty set: the only mask has no entry `true`, and `r = 0`.
    simp_all [rank, count_unrank]
  | case3 L m r h ih =>
    -- Level 1 belongs to the set.
    simpa [rank] using ih h
  | case4 L m r h ih =>
    -- Level 1 does not belong to the set: the `(L choose m)` masks with level 1 come before.
    rw [Nat.choose_succ_succ'] at hr
    have hrest : r - L.choose m < L.choose (m + 1) := by omega
    simp only [rank, count_unrank hrest, length_unrank, ih hrest, Nat.succ_ne_zero, if_false,
      Nat.add_sub_cancel]
    omega

/-- Different numbers give different masks. -/
 theorem eq_of_unrank_eq {L m r r' : ℕ} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : unrank L m r = unrank L m r') : r = r' := by
  rw [← rank_unrank hr, ← rank_unrank hr', h]

/-! ## Masks and sets of levels -/

/-- The set of levels of a mask. -/
def maskSet (L : ℕ) (mask : List Bool) : Finset (Fin L) :=
  Finset.univ.filter fun ℓ => mask.getD ℓ false

/-- The mask of a set of levels. -/
def maskOf {L : ℕ} (Q : Finset (Fin L)) : List Bool := List.ofFn fun ℓ => decide (ℓ ∈ Q)










/-- The number of levels of a mask is the number of its entries `true`. -/
 theorem card_maskSet {L : ℕ} (mask : List Bool) (h : mask.length = L) :
    (maskSet L mask).card = mask.count true := by
  induction mask generalizing L with
  | nil =>
    subst h
    simp [maskSet]
  | cons x l ih =>
    -- Split off level 1.
    subst h
    have hrest := ih rfl
    unfold maskSet at hrest ⊢
    rw [List.length_cons, Fin.card_filter_univ_succ]
    cases x <;> simpa using hrest

/-- The set of levels of a mask of the enumeration has `m` elements. -/
theorem card_maskSet_unrank {L m r : ℕ} (hr : r < L.choose m) :
    (maskSet L (unrank L m r)).card = m := by
  rw [card_maskSet _ (length_unrank L m r), count_unrank hr]

/-- The mask of the set of levels of a mask of length `L` is that mask. -/
theorem maskOf_maskSet {L : ℕ} (mask : List Bool) (h : mask.length = L) :
    maskOf (maskSet L mask) = mask := by
  subst h
  refine List.ext_getElem (by simp [maskOf]) fun i _ _ => ?_
  simp [maskOf, maskSet]

/-- Different numbers give different sets of levels. -/
theorem eq_of_maskSet_unrank_eq {L m r r' : ℕ} (hr : r < L.choose m) (hr' : r' < L.choose m)
    (h : maskSet L (unrank L m r) = maskSet L (unrank L m r')) : r = r' := by
  refine eq_of_unrank_eq hr hr' ?_
  rw [← maskOf_maskSet _ (length_unrank L m r), h, maskOf_maskSet _ (length_unrank L m r')]

/-! ## From one mask to the next -/











































































end ThreeSumApsp.Spec

