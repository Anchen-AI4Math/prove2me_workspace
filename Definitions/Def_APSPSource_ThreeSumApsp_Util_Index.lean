/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.Order.Ring.Int

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Index arithmetic: a pair of numbers as one number

General facts about natural numbers. A matrix with rows of length `n` is kept as one list, row
after row: the entry in row `a` and column `b < n` has the index `a * n + b`. This file has

* the bounds on such an index (`Nat.mul_add_lt_mul`, `Nat.mul_add_le_mul`);
* the way back from the index to the pair (`Nat.mul_add_div_of_lt`, `Nat.mul_add_inj_of_lt`,
  `Nat.div_lt_of_lt_mul'`, `Nat.mod_lt_of_lt_mul`, `Nat.exists_eq_mul_add_of_lt_mul`,
  `Nat.eq_mul_succ_iff`);
* the pair of the next index (`Nat.succ_div_mod_of_lt`, `Nat.succ_div_mod_of_ne`,
  `Nat.succ_div_mod_of_eq`);
* residues seen as natural numbers (`Int.toNat_emod_lt`, `Int.natCast_toNat_emod`).
-/

public section

namespace Nat

/-! ## Bounds on an index -/

/-- The index of an entry of a matrix with `m` rows and `n` columns is below `m * n`. -/
theorem mul_add_lt_mul {a b m n : ℕ} (ha : a < m) (hb : b < n) : a * n + b < m * n :=
  Nat.mul_comm a n ▸ Nat.mul_add_lt_mul_of_lt_of_lt ha hb







/-! ## From the index back to the pair

The column is `Nat.mul_add_mod_of_lt : c < b → (a * b + c) % b = c`. -/

/-- The row of the index `a * n + b`. -/
theorem mul_add_div_of_lt {a b n : ℕ} (hb : b < n) : (a * n + b) / n = a := by
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.zero_lt_of_lt hb), Nat.div_eq_of_lt hb, Nat.add_zero]

/-- The index determines the pair. -/
theorem mul_add_inj_of_lt {a b a' b' n : ℕ} (hb : b < n) (hb' : b' < n)
    (h : a * n + b = a' * n + b') :
    a = a' ∧ b = b' :=
  ⟨by rw [← mul_add_div_of_lt (a := a) hb, h, mul_add_div_of_lt hb'],
    by rw [← Nat.mul_add_mod_of_lt (a := a) hb, h, Nat.mul_add_mod_of_lt hb']⟩






















/-! ## The next index -/























end Nat

namespace Int

/-! ## Residues as natural numbers -/

/-- The residue of an integer modulo `M ≥ 1`, as a natural number, is below `M`. -/
theorem toNat_emod_lt {M : ℕ} (hM : 0 < M) (x : ℤ) : (x % (M : ℤ)).toNat < M := by
  have := Int.emod_lt_of_pos x (Int.natCast_pos.2 hM)
  omega





end Int

