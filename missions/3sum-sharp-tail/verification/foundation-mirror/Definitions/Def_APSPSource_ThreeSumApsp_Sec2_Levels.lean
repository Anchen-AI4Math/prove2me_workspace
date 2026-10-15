/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option relaxedAutoImplicit false


/-!
# Strings cut along a set of levels

Section 2.3.3 cuts a string of `L` variables along a set `Q` of `m` levels: its variables
at the levels of `Q`, in the order of the levels, form a string of length `m`, and its variables at
the other levels form a string of length `L - m`. The first three parts of this file hold for every
alphabet; the last part specializes them to left, right and output strings.

* Every level is the `k`-th lowest level of `Q` or the `k`-th lowest level outside `Q` for some `k`.
  So a statement about all levels is checked on these two kinds of levels (`forall_level_iff`), and
  so is the statement that a set of levels is `Q` (`filter_eq_iff_forall_level`).
* `glue Q hQ f g` is the string with the letters of `f` at the levels of `Q` and the letters of `g`
  at the other levels. It is the only such string (`eq_glue_iff`), and `f` and `g` can be read off
  it (`glue_inj`).
* If the letters are of two kinds, inner and outer, and each is given by its kind and an index, then
  a string can be rebuilt from its inner set and the indices of its letters (`glue_index`).
* "A string is determined by its inner set, its outer part, and its inner part": the strings
  `leftStrOf Q hQ r π`, `rightStrOf Q hQ π c` and `outStrOf Q hQ r c` have the parts that their
  names say, and no other string has them (`existsUnique_leftStr`, `existsUnique_rightStr`,
  `existsUnique_outStr`). No later proof uses these three statements; the later proofs use the
  lemmas from which they follow.
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m : ℕ} (Q : Finset (Fin L)) (hQ : Q.card = m)

/-! ### The levels of a set and of its complement, in order -/






















































/-! ### Gluing two strings along a set of levels -/

variable {α : Type*}

/-- The string that has the letters of `f` at the levels of `Q` and the letters of `g` at the other
levels, both in the order of the levels. -/
def glue (f : Fin m → α) (g : Fin (L - m) → α) : Fin L → α :=
  fun ℓ =>
    if hℓ : ℓ ∈ Q then f ((Q.orderIsoOfFin hQ).symm ⟨ℓ, hℓ⟩)
    else g ((Qᶜ.orderIsoOfFin (card_compl_of_card_eq Q hQ)).symm ⟨ℓ, mem_compl.mpr hℓ⟩)




























variable {f f' : Fin m → α} {g g' : Fin (L - m) → α}


















/-! ### Alphabets with inner and outer letters -/

variable (IsInner : α → Prop) [DecidablePred IsInner]




















/-! ### Left, right and output strings with a given inner set, outer part and inner part -/

/-- The left string with inner set `Q`, outer part `r` and inner part `π`. -/
def leftStrOf (r : OuterStr L m) (π : InnerStr m) : LeftStr L :=
  glue Q hQ (fun k => .p (π k).1 (π k).2) (fun k => .x (r k))

/-- The right string with inner set `Q`, inner part `π` and outer part `c`. -/
def rightStrOf (π : InnerStr m) (c : OuterStr L m) : RightStr L :=
  glue Q hQ (fun k => .q (π k).1 (π k).2) (fun k => .y (c k))

/-- The output string with inner set `Q`, row `r` and column `c` (Section 2.3.3: "the output strings
with inner set Q index the entries of the product X_Q Y_Q"): it has `z₀` at the levels of `Q`, and
at the `k`-th lowest level outside `Q` it has `z_{r_k c_k}`. -/
def outStrOf (r c : OuterStr L m) : OutStr L :=
  glue Q hQ (fun _ => .z0) (fun k => .z (r k) (c k))
































































variable {Q}



































variable {hQ}

















variable (Q) (hQ)
include hQ




































end ThreeSumApsp

