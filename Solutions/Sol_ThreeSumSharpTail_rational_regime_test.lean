/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ThreeSumSharpTailRationalRegimeTest

open Light

/-- A straight-line expression for a natural power, using only multiplication. -/
def powExpr (x k : ℕ) : Expr :=
  match k with
  | 0 => .const 1
  | k + 1 => .op .mul (.var x) (powExpr x k)

theorem powExpr_val (σ : State) (x k : ℕ) :
    (powExpr x k).val σ = σ.loc x ^ k := by
  induction k with
  | zero => simp [powExpr, Expr.val]
  | succ k ih => simp [powExpr, Expr.val, Op.eval, ih, pow_succ, mul_comm]

theorem pow_le_pow_of_one_le {n : ℕ} (hn : 1 ≤ n) {i j : ℕ} (hij : i ≤ j) :
    n ^ i ≤ n ^ j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  have hk : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn
  calc
    n ^ i = n ^ i * 1 := by simp
    _ ≤ n ^ i * n ^ k := Nat.mul_le_mul_left _ hk

theorem powExpr_safe (lim : Limits) (σ : State) (x base exponent : ℕ)
    (hbase : 1 ≤ base) (hloc : σ.loc x = (base : ℤ))
    (hword : (base ^ exponent : ℕ) ≤ lim.word) :
    (powExpr x exponent).Safe lim σ := by
  induction exponent with
  | zero => simpa [powExpr, Expr.Safe] using hword
  | succ k ih =>
      simp only [powExpr, Expr.Safe, Expr.val, Op.eval]
      constructor
      · trivial
      constructor
      · apply ih
        have hmono : base ^ k ≤ base ^ (k + 1) :=
          pow_le_pow_of_one_le hbase (by omega)
        have hcast : (base ^ k : ℤ) ≤ (base ^ (k + 1) : ℤ) := by exact_mod_cast hmono
        exact hcast.trans hword
      · have hv : (powExpr x k).val σ * σ.loc x = (base ^ (k + 1) : ℕ) := by
          rw [powExpr_val, hloc]
          norm_cast
        rw [mul_comm (σ.loc x) ((powExpr x k).val σ), hv,
          abs_of_nonneg (Int.natCast_nonneg _)]
        exact_mod_cast hword

def program (A B : ℕ) : Stmt :=
  .seq (.set 2 (powExpr 0 A))
    (.seq (.set 3 (powExpr 1 B))
      (.ite (.lt (.var 2) (.var 3)) (.set 0 (.const 0)) (.set 0 (.const 1))))

def stepCount (A B : ℕ) : ℕ :=
  ((powExpr 0 A).cost + 1) + ((powExpr 1 B).cost + 1 + 6)

theorem solution (A B : ℕ) :
    ∃ (S : Stmt) (c : ℕ),
      ∀ (lim : Limits) (P : Program) (d : ℕ) (N D : ℕ) (μ : ℕ → ℤ),
        1 ≤ N → 1 ≤ D →
        ((N ^ A + D ^ B + 100 : ℕ) : ℤ) ≤ lim.word →
        Ends lim P d S ⟨frame [N, D], μ⟩ c
          (fun σ => σ.mem = μ ∧
            ((σ.loc 0 = 1 ∧ D ^ B ≤ N ^ A) ∨ (σ.loc 0 = 0 ∧ N ^ A < D ^ B))) := by
  refine ⟨program A B, stepCount A B, ?_⟩
  intro lim P d N D μ hN hD hword
  let σ₀ : State := ⟨frame [N, D], μ⟩
  let σ₁ : State := { σ₀ with loc := Function.update σ₀.loc 2 ((powExpr 0 A).val σ₀) }
  let σ₂ : State := { σ₁ with loc := Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) }
  let cnd : Cond := .lt (.var 2) (.var 3)
  have hwordA : (N ^ A : ℕ) ≤ lim.word := by
    have hlt : N ^ A ≤ N ^ A + D ^ B + 100 := by omega
    exact (show (N ^ A : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) by exact_mod_cast hlt).trans hword
  have hwordB : (D ^ B : ℕ) ≤ lim.word := by
    have hlt : D ^ B ≤ N ^ A + D ^ B + 100 := by omega
    exact (show (D ^ B : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) by exact_mod_cast hlt).trans hword
  have hsafeA : (powExpr 0 A).Safe lim σ₀ := by
    apply powExpr_safe lim σ₀ 0 N A hN
    · simp [σ₀, frame]
    · exact hwordA
  have hsafeB : (powExpr 1 B).Safe lim σ₁ := by
    apply powExpr_safe lim σ₁ 1 D B hD
    · simp [σ₁, σ₀, frame]
    · exact hwordB
  have hvalA : (powExpr 0 A).val σ₀ = (N ^ A : ℕ) := by
    rw [powExpr_val]
    simp [σ₀, frame]
  have hvalB : (powExpr 1 B).val σ₁ = (D ^ B : ℕ) := by
    rw [powExpr_val]
    simp [σ₁, σ₀, frame]
  have hcnd : cnd.Safe lim σ₂ := by
    simp [cnd, Cond.Safe]
  have hcondval : cnd.Holds σ₂ ↔ (N ^ A : ℤ) < D ^ B := by
    change σ₂.loc 2 < σ₂.loc 3 ↔ _
    have hloc2 : σ₂.loc 2 = (N ^ A : ℤ) := by simp [σ₂, σ₁, σ₀, hvalA]
    have hloc3 : σ₂.loc 3 = (D ^ B : ℤ) := by
      change Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) 3 = _
      simp [hvalB]
    rw [hloc2, hloc3]
  have hseqA : Exec lim P d (.set 2 (powExpr 0 A)) σ₀ σ₁ ((powExpr 0 A).cost + 1) := by
    simpa [σ₁, σ₀] using (Exec.set hsafeA : Exec lim P d (.set 2 (powExpr 0 A)) σ₀
      { σ₀ with loc := Function.update σ₀.loc 2 ((powExpr 0 A).val σ₀) } ((powExpr 0 A).cost + 1))
  have hseqB : Exec lim P d (.set 3 (powExpr 1 B)) σ₁ σ₂ ((powExpr 1 B).cost + 1) := by
    simpa [σ₂] using (Exec.set hsafeB : Exec lim P d (.set 3 (powExpr 1 B)) σ₁
      { σ₁ with loc := Function.update σ₁.loc 3 ((powExpr 1 B).val σ₁) } ((powExpr 1 B).cost + 1))
  have hword100 : (100 : ℤ) ≤ lim.word := by
    have : (100 : ℤ) ≤ (N ^ A + D ^ B + 100 : ℕ) := by exact_mod_cast (by omega : 100 ≤ N ^ A + D ^ B + 100)
    exact this.trans hword
  by_cases hlt : (N ^ A : ℤ) < D ^ B
  · have hbranch : Exec lim P d (.set 0 (.const 0)) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 0 } 2 := by
      exact Exec.set (by simp [Expr.Safe]; omega)
    have hite : Exec lim P d (.ite cnd (.set 0 (.const 0)) (.set 0 (.const 1))) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 0 }
        (cnd.cost + 1 + 2) :=
      Exec.iteTrue hcnd (hcondval.mpr hlt) hbranch
    have hexec : Exec lim P d (program A B) σ₀
        { σ₂ with loc := Function.update σ₂.loc 0 0 } (stepCount A B) := by
      simpa [program, stepCount, cnd, Cond.cost] using Exec.seq hseqA (Exec.seq hseqB hite)
    refine ⟨_, stepCount A B, hexec, le_rfl, ?_⟩
    constructor
    · simp [σ₂, σ₁, σ₀, Function.update]
    · right
      constructor
      · simp [σ₂, σ₁, σ₀, Function.update, hvalA, hvalB]
      · exact_mod_cast hlt
  · have hbranch : Exec lim P d (.set 0 (.const 1)) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 1 } 2 := by
      exact Exec.set (by simp [Expr.Safe]; omega)
    have hite : Exec lim P d (.ite cnd (.set 0 (.const 0)) (.set 0 (.const 1))) σ₂
        { σ₂ with loc := Function.update σ₂.loc 0 1 }
        (cnd.cost + 1 + 2) :=
      Exec.iteFalse hcnd (fun hh => hlt (hcondval.mp hh)) hbranch
    have hexec : Exec lim P d (program A B) σ₀
        { σ₂ with loc := Function.update σ₂.loc 0 1 } (stepCount A B) := by
      simpa [program, stepCount, cnd, Cond.cost] using Exec.seq hseqA (Exec.seq hseqB hite)
    refine ⟨_, stepCount A B, hexec, le_rfl, ?_⟩
    constructor
    · simp [σ₂, σ₁, σ₀, Function.update]
    · left
      constructor
      · simp [σ₂, σ₁, σ₀, Function.update, hvalA, hvalB]
      · have hnlt : ¬ ((N ^ A : ℤ) < D ^ B) := hlt
        exact_mod_cast (not_lt.mp hnlt)

end ThreeSumSharpTailRationalRegimeTest
