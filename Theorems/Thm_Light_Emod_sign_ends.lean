/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_Light_neg_emod_nat


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false


theorem Light.Emod.sign_ends : ∀ {lim : Light.Limits} {P : Light.Program} {d : Nat} {x : Int} {Mo V fr a : Nat} (F : Light.Emod.Pre lim Mo V fr)
  (hax : @Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt a) (@abs.{0} Int instLatticeInt Int.instAddGroup x))
  {μ' : Nat → Int} {t : Int},
  Light.Ends lim P d Light.emodSign
    {
      loc :=
        Light.frame
          (@List.cons.{0} Int x
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt Mo)
              (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt fr)
                (@List.cons.{0} Int
                  (@Nat.cast.{0} Int instNatCastInt
                    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a Mo))
                  (@List.cons.{0} Int (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0)))
                    (@List.cons.{0} Int t (@List.nil.{0} Int))))))),
      mem := μ' }
    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) fun (σ' : Light.State) =>
    And
      (@Eq.{1} Int (σ'.loc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod) x (@Nat.cast.{0} Int instNatCastInt Mo)))
      (@Eq.{1} (Nat → Int) σ'.mem μ') := by
  sorry

