/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec2_Theorem5_Subsets
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Bool.Count
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The table of subsets: how a row is made from the row before it

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  The programs keep them in a table.  Row number `s` of the
table is the mask `Spec.unrank L m s`, as `L` cells 1 and 0 (`bit`).  No program occurs here.

* The first row is `m` ones followed by zeros (`bit_unrank_zero`).
* Two consecutive masks are `pre 1 0 0^a 1^b` and `pre 0 1 1^b 0^a` (`Spec.unrank_succ_shape`).  So
  one pass from the end of the old row finds `b` and the length of `pre`: `scanAt` is the state of
  this scan after a number of rounds, and `scanAt_shape` is what it has found after all rounds.
* A second pass writes the new row: `newCell` is the cell that it writes (`bit_unrank_succ`), and
  the numbers that it computes on the way are small (`scanAt_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec.Subsets

/-- A truth value as a cell. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

















/-! ## The backward scan -/

/-- The state of the scan: the phase (0 while the ones at the end of the row are counted, 1 while
the zeros before them are passed, 2 when the 1 before these zeros has been found), the number of
ones at the end of the row, and the position of the 1 that was found.  The three fields are the
contents of three local variables of the routine, so they are integers, and `scanStep` and `newCell`
compare them by `<`, the comparison of the language. -/
structure Scan where
  /-- The phase: 0, 1 or 2. -/
  phase : ℤ
  /-- The number of ones at the end of the row. -/
  ones : ℤ
  /-- The position of the last 1 that is followed by a 0. -/
  pos : ℤ

/-- The result of a scan fits into a row of `L` cells: the position `p` and the number `b` of ones
are natural numbers with `p + 2 + b ≤ L`. -/
def Scan.Fits (S : Scan) (L : ℕ) : Prop := 0 ≤ S.pos ∧ 0 ≤ S.ones ∧ S.pos + 2 + S.ones ≤ L

/-- One round of the scan: `x` is the cell that is read, and `q` its position. -/
def scanStep (x q : ℤ) (S : Scan) : Scan :=
  if S.phase < 1 then (if x < 1 then { S with phase := 1 } else { S with ones := S.ones + 1 })
  else if S.phase < 2 then (if x < 1 then S else { S with phase := 2, pos := q })
  else S

/-- The state of the scan of a row of length `L` after `j` rounds. -/
def scanAt (row : ℕ → ℤ) (L : ℕ) : ℕ → Scan
  | 0 => ⟨0, 0, 0⟩
  | j + 1 => scanStep (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)


















section shape
variable {pre : List Bool} {a b L : ℕ} {row : ℕ → ℤ} (hL : L = pre.length + 2 + a + b)
  (hrow : ∀ q < L, row q =
    bit ((pre ++ true :: false :: (List.replicate a false ++ List.replicate b true)).getD q false))
include hL hrow
















































end shape

/-! ## The writing pass -/

/-- The cell number `q` of the new row, from the cell of the old row and the result of the scan. -/
def newCell (S : Scan) (old q : ℤ) : ℤ :=
  if q < S.pos then old else if q < S.pos + 1 then 0 else if q < S.pos + 2 + S.ones then 1 else 0

section next
variable {L m s : ℕ} (hs : s + 1 < L.choose m) {row : ℕ → ℤ}
  (hrow : ∀ q < L, row q = bit ((Spec.unrank L m s).getD q false))
include hs hrow



















end next

end ThreeSumApsp.Spec.Subsets

