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



theorem ThreeSumApsp.Spec.mem_nineStrs : ∀ {n lo hi : Nat} (l : List.{0} Nat),
  Iff
    (@Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat))
      (ThreeSumApsp.Spec.nineStrs n lo hi) l)
    (And (@Eq.{1} Nat (@List.length.{0} Nat l) n)
      (And
        (∀ (d : Nat),
          @Membership.mem.{0, 0} Nat (List.{0} Nat) (@List.instMembership.{0} Nat) l d →
            @LT.lt.{0} Nat instLTNat d (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))
        (And
          (@LE.le.{0} Nat instLENat lo
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l))
          (@LE.le.{0} Nat instLENat
            (@List.count.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
              (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9))) l)
            hi)))) := by
  sorry

