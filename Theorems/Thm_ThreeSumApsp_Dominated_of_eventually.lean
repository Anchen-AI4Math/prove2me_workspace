/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Util_Asymptotics_Dominated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false



theorem ThreeSumApsp.Dominated.of_eventually : ∀ {f g : Nat → Real} {C : Real},
  @Filter.Eventually.{0} Nat
      (fun (n : Nat) =>
        @LE.le.{0} Real Real.instLE (f n)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) C (g n)))
      (@Filter.atTop.{0} Nat Nat.instPreorder) →
    ∀ {n₀ : Nat},
      (∀ (n : Nat),
          @LE.le.{0} Nat instLENat n₀ n →
            @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
              (g n)) →
        @ThreeSumApsp.Dominated.{0} Nat (fun (n : Nat) => @LE.le.{0} Nat instLENat n₀ n) f g := by
  sorry

