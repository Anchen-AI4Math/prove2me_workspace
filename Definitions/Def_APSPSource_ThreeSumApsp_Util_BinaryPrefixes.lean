/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The prefixes of a binary representation, one bit at a time

The prefixes `⌊z/2^ℓ⌋` of a number `0 ≤ z < 2^L` are computed without division, from the level
`ℓ = L` down to `ℓ = 0`.  Next to the prefix `q = ⌊z/2^ℓ⌋` (`prefQ`) one keeps the rest of the
number, moved to the top: `r = (z mod 2^ℓ) 2^(L-ℓ) < 2^L` (`prefR`).  One step doubles `r`; if the
result reaches `2^L`, then the next bit of `z` is 1 (`pref_step`).  The bit is the binary digit
number `ℓ` of `z` (`testBit_iff_shift`).  One step on lists of numbers is `zipWith_shiftQ` and
`map_shiftR`.
-/

@[expose] public section

namespace ThreeSumApsp

/-! ## Prefixes, one bit at a time -/

/-- The prefix `⌊z/2^ℓ⌋`. -/
def prefQ (ℓ : ℕ) (z : ℤ) : ℤ := z / 2 ^ ℓ

/-- The rest `z mod 2^ℓ`, moved to the top of `L` bits. -/
def prefR (L ℓ : ℕ) (z : ℤ) : ℤ := z % 2 ^ ℓ * 2 ^ (L - ℓ)

/-- The new prefix after one step: the old one with the next bit appended. -/
def shiftQ (P q r : ℤ) : ℤ := if 2 * r < P then 2 * q else 2 * q + 1

/-- The new rest after one step. -/
def shiftR (P r : ℤ) : ℤ := if 2 * r < P then 2 * r else 2 * r - P










































































/-! ## The lists of the prefixes and of the rests -/




















end ThreeSumApsp

