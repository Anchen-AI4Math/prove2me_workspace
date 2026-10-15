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
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Matrices in Z-order (Morton order)

The count of the proof of Theorem 17 needs a product of matrices over `ℤ[x]/(x^p - 1)`, "O(n^{log₂
7}) with Strassen's algorithm".  For the recursion of that algorithm a `2^K × 2^K` matrix is stored
in Z-order: the entry `(a, c)` stands at the place whose digits in base 4 are `2 a_i + c_i`, where
`a_i` and `c_i` are the binary digits of `a` and `c`.

* Places: `zIdx` maps a pair to its place, `zRow` and `zCol` map back (`zRow_zIdx`, `zCol_zIdx`,
  `zIdx_zRow_zCol`).  All three are computed one digit in base 4 at a time (`zIdx_eq`, `zRow_eq`,
  `zCol_eq`), and every proof is an induction along these equations.
* Lists: the entry `(a, c)` of `zList K M` starts at `zIdx a c * p` (`getD_zList`).
* **The four quadrants of a matrix are the four quarters of its list** (`quarter_zList`,
  `zList_succ`), which is what the recursion needs.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## Places -/

/-- The binary digits of `i`, moved to the even places: the number with the same digits in
base 4. -/
def spread (i : ℕ) : ℕ := Nat.ofDigits 4 (Nat.digits 2 i)

/-- The table of `spread`. -/
def spreadList (N2 : ℕ) : List ℤ := (List.range N2).map fun i : ℕ => ((spread i : ℕ) : ℤ)

/-- The place of the entry `(a, c)` in Z-order. -/
def zIdx (a c : ℕ) : ℕ := 2 * spread a + spread c

/-- The row of the entry at place `z`. -/
def zRow (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· / 2))

/-- The column of the entry at place `z`. -/
def zCol (z : ℕ) : ℕ := Nat.ofDigits 2 ((Nat.digits 4 z).map (· % 2))





































































































/-! ## Matrices as lists -/

/-- A `2^K × 2^K` matrix of vectors, as one list, entry after entry in Z-order. -/
def zList (K : ℕ) (M : ℕ → ℕ → List ℤ) : List ℤ :=
  (List.range (4 ^ K)).flatMap fun z => M (zRow z) (zCol z)

/-- The quarter number `t` of a list of length `4 q`. -/
def quarter (q t : ℕ) (l : List ℤ) : List ℤ := (l.drop (t * q)).take q

















































end ThreeSumApsp.Spec

