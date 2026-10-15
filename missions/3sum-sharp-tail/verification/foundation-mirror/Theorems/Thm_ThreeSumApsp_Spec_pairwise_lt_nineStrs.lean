/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Spec_Sec4_Theorem30_NineStrings
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



theorem ThreeSumApsp.Spec.pairwise_lt_nineStrs : ∀ (n lo hi : Nat),
  @List.Pairwise.{0} (List.{0} Nat)
    (fun (x1 x2 : List.{0} Nat) => @LT.lt.{0} (List.{0} Nat) (@List.instLT.{0} Nat instLTNat) x1 x2)
    (ThreeSumApsp.Spec.nineStrs n lo hi) := by
  sorry

