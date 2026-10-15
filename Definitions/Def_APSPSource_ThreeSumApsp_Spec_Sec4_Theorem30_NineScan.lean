/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Count
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# The successor of a string, as two passes from left to right

`nineNext`, which goes from a string with a bounded number of nines to the next one, is defined by
recursion on the string.  A machine goes through the cells of a buffer from left to right.  This
file gives the function in that shape.

* One pass over the string finds the last position whose digit can be raised, and the number of
  nines before it (`nineScan`).
* A second pass writes the next string: the digits before that position are kept, its digit is
  raised by one, and the rest is filled with zeros followed by nines (`raiseAt`).

The result is `nineNext_eq_scan`.  It is proved in two steps: `nineNext` raises the last position
that can be raised (`raisePos`, `nineNext_eq_raise`), and the scan finds that position
(`nineScanFrom_eq`).  For the routine there are, besides, an invariant of the scan
(`nineScan_inv`) and the fact that the filling fits behind the position that is raised
(`raise_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The last position that can be raised -/

/-- Whether the digit d can be raised when c nines come before it and at most hi nines are
allowed. -/
def canRaise (hi c d : ℕ) : Bool := decide (d < 8) || (decide (d = 8) && decide (c < hi))

/-- The last position of the string whose digit can be raised, with the number of nines before it;
c nines come before the string. -/
 def raisePos (hi : ℕ) : ℕ → List ℕ → Option (ℕ × ℕ)
  | _, [] => none
  | c, d :: l =>
    match raisePos hi (if d = 9 then c + 1 else c) l with
    | some (p, c') => some (p + 1, c')
    | none => if canRaise hi c d then some (0, c) else none

/-- The string with the digit at position p raised by one and the least admissible filling behind
it; c nines come before p. -/
def raiseAt (lo p c : ℕ) (l : List ℕ) : List ℕ :=
  l.take p ++ (l.getD p 0 + 1) ::
    nineFirst (l.length - p - 1) (lo - c - if l.getD p 0 = 8 then 1 else 0)





































/-! ## The scan from left to right -/

/-- The state of the scan: 1 if a position that can be raised has been seen, the last such
position, the number of nines before it, and the number of nines seen so far. -/
structure NineScan where
  found : ℕ
  pos : ℕ
  before : ℕ
  nines : ℕ

/-- One step of the scan: the cell number i holds the digit d. -/
def nineScanStep (hi i d : ℕ) (s : NineScan) : NineScan :=
  { found := if canRaise hi s.nines d then 1 else s.found
    pos := if canRaise hi s.nines d then i else s.pos
    before := if canRaise hi s.nines d then s.nines else s.before
    nines := if d = 9 then s.nines + 1 else s.nines }

/-- The scan of a list whose first cell has the number i. -/
def nineScanFrom (hi : ℕ) : ℕ → List ℕ → NineScan → NineScan
  | _, [], s => s
  | i, d :: l, s => nineScanFrom hi (i + 1) l (nineScanStep hi i d s)

/-- The state after the first j cells. -/
def nineScan (hi : ℕ) (l : List ℕ) (j : ℕ) : NineScan := nineScanFrom hi 0 (l.take j) ⟨0, 0, 0, 0⟩






















































/-! ## What the scan has found -/

/-- What holds of the state s of the scan after j cells: the counter holds the number of nines
among them, and the position found, if any, is one of them, can be raised, and has the recorded
number of nines before it. -/
structure NineScanInv (hi : ℕ) (l : List ℕ) (j : ℕ) (s : NineScan) : Prop where
  nines : s.nines = (l.take j).count 9
  found : s.found = 0 ∨ s.found = 1
  pos_lt : s.found = 1 → s.pos < j
  canRaise : s.found = 1 → canRaise hi s.before (l.getD s.pos 0) = true
  before : s.found = 1 → s.before = (l.take s.pos).count 9
























/-! ## The filling fits -/














end ThreeSumApsp.Spec

