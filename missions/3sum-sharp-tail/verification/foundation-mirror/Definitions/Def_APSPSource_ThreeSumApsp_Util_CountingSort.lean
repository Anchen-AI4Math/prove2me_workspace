/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.SuccPred

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The pure side of counting sort

`N` items `0, …, N - 1` have keys `kf 0, …, kf (N - 1)`.  A stable sort by key puts item `j` at the
place `sortPos kf N j`: the number of items with a smaller key plus the number of earlier items with
the same key.

This is a bijection of `{0, …, N - 1}` (`eq_of_sortPos_eq`, `exists_sortPos_eq`) that is increasing
for the order "smaller key, or same key and earlier" (`sortPos_lt_sortPos_iff`).
-/

@[expose] public section

namespace ThreeSumApsp

/-- The number of items `i < j` with key `t`. -/
def cntEq (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i = t) j

/-- The number of items `i < j` with a key smaller than `t`. -/
def cntLt (kf : ℕ → ℕ) (t j : ℕ) : ℕ := Nat.count (fun i => kf i < t) j

/-- The place of item `j` after a stable sort of the items `0, …, N - 1` by key. -/
def sortPos (kf : ℕ → ℕ) (N j : ℕ) : ℕ := cntLt kf (kf j) N + cntEq kf (kf j) j

section
variable (kf : ℕ → ℕ)






























end

variable {kf : ℕ → ℕ} {N K : ℕ}



























































end ThreeSumApsp

