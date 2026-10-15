import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ThreeSum1960614

noncomputable def entropy (t : ℝ) : ℝ := Real.binEntropy t / Real.log 2
noncomputable def E (c : ℕ) : ℝ := (c : ℝ) / 2 * entropy (1 / c)
noncomputable def kappa (c : ℕ) : ℝ :=
  2 * c * entropy (1 / (2 * c)) - c * entropy (1 / c) - 1
noncomputable def gamma (c : ℕ) (t : ℝ) : ℝ :=
  c * entropy (1 / c) - c * entropy ((1 - t) / c)
def phi (t : ℝ) : ℝ :=
  (785174904 * t + 72447023 * t ^ 2 + 24044466 * t ^ 3 + 12022459 * t ^ 4) / 100000000
def phiDeriv (t : ℝ) : ℝ :=
  (785174904 + 2 * 72447023 * t + 3 * 24044466 * t ^ 2 + 4 * 12022459 * t ^ 3) / 100000000
def epsilon : ℝ := 203889696 / 1000000000
def beta : ℝ := -(62656016 / 1000000000)
def saving : ℝ := 193175570 / 1000000000
def theta : ℝ := 40409899 / 1000000000
def tau : ℝ := 13 / 20
def rho : ℝ := 2790503 / 10000000
def tangentPoint : ℝ := 17200068185091493 / 100000000000000000
def principal : ℝ := 196061388 / 100000000
def target : ℚ := 1960614 / 1000000
def v : ℝ := saving - 2 * beta
def threshold (a : ℝ) : ℝ := (v + a) / (1 - a)
def ledger (e b S terminal ratio EE kk hh : ℝ) : List ℝ :=
  [2 * e * EE,
   1 + e * (EE - b),
   2 - e * S,
   2 - e * (1 / 2 + b - hh),
   2 - e * (1 / 2 - b - kk - ratio * (1 + S - 2 * b)),
   2 - e * (terminal - 1 / 2 - b - kk),
   e * (8 / 5) * (EE + 1 / 2),
   2 + e * (4 / 5 - (2 / 5) * EE - 2 * b),
   1 + e * (1 / 2 - b),
   2 - e * (EE + b),
   2 - 2 * e * (EE + b), 1]
noncomputable def costs : List ℝ :=
  ledger epsilon beta saving tau rho (E 232) (kappa 232) (entropy theta)
def clearedSwitch (J s j q : ℕ) : Prop :=
  let r := (J - j) * s
  500000000 * (J - j) *
    (785174904 * q * r ^ 3 + 72447023 * q ^ 2 * r ^ 2 +
     24044466 * q ^ 3 * r + 12022459 * q ^ 4) ≥
    100000000 * (159243801 * J + 500000000 * j) * r ^ 4
noncomputable def ModelFeasible (c : ℕ) (e b S th terminal ratio R : ℝ) : Prop :=
  0 < e ∧ e < 1 ∧ b < 0 ∧ 0 < S ∧
  0 ≤ th ∧ th ≤ 1 / 2 ∧ 0 ≤ terminal ∧ terminal < 1 ∧
  0 < ratio ∧ S - 2 * b ≤ gamma c th ∧
  (∀ t ∈ Set.Icc (0 : ℝ) (1 / 2), entropy t ≤ ratio * (1 + gamma c t)) ∧
  ∀ z ∈ ledger e b S terminal ratio (E c) (kappa c) (entropy th), z ≤ R

end ThreeSum1960614

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

/-! Claims of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse Lopsided Graphs» (Josh
Alman, Virginia Vassilevska Williams), about programs of a word RAM defined here. Imports nothing, proves nothing. -/

@[expose] public section

namespace EndStatement

/-- `i j k` name cells, `l` a position in the program, `[i]` is the word in cell `i`. The only constant is 1. -/
inductive Instr where
  | one (i : Int)             -- [i] := 1
  | add (i j k : Int)         -- [i] := [j] + [k]
  | sub (i j k : Int)         -- [i] := [j] - [k]
  | mul (i j k : Int)         -- [i] := [j] * [k]
  | load (i j : Int)          -- [i] := [[j]]
  | store (i j : Int)         -- [[i]] := [j]
  | bltz (i : Int) (l : Nat)  -- if [i] < 0, go to position l
  | accept
  | reject

/-- The verdict and the final memory, if `P`, run from position `pc` on memory `m`, halts within `t` steps, the halting
step counted; past its end `P` rejects. Addresses are read signed; `bltz` jumps on a negative word; `write` runs on. -/
def exec {W : Nat} (P : List Instr) : (t pc : Nat) → (m : Int → BitVec W) → Option (Bool × (Int → BitVec W))
  | 0, _, _ => none
  | t + 1, pc, m =>
    let write (i : Int) (v : BitVec W) := exec P t (pc + 1) fun x => if x = i then v else m x
    match P.getD pc .reject with
    | .one i => write i 1
    | .add i j k => write i (m j + m k)
    | .sub i j k => write i (m j - m k)
    | .mul i j k => write i (m j * m k)
    | .load i j => write i (m (m j).toInt)
    | .store i j => write (m i).toInt (m j)
    | .bltz i l => exec P t (if (m i).toInt < 0 then l else pc + 1) m
    | .accept => some (true, m)
    | .reject => some (false, m)

/-- The memory at the start: `ws` in cells 0, 1, 2, …, and 0 in every other cell. -/
def loadWords (W : Nat) (ws : List Int) : Int → BitVec W :=
  fun a => if a < 0 then 0 else BitVec.ofInt W (ws.getD a.toNat 0)

/-- `T(n) = O(n^r)`, both sides raised to the power `r.den`: core Lean has no fractional powers. For `r = 1.9992 =
2499/1250` it says `T(n)^1250 ≤ K n^2499`. -/
def BigO (T : Nat → Nat) (r : Rat) : Prop :=
  ∃ K : Nat, ∀ n ≥ 2, T n ^ r.den ≤ K * n ^ r.num.toNat

/-- `yes`: when to accept (always, if not given). `output`: a condition on the cells after the input, read as signed. -/
structure Problem where
  Instance : Nat → Type
  input {n : Nat} : Instance n → List Int
  yes {n : Nat} : Instance n → Prop := fun _ => True
  output {n : Nat} : Instance n → (Nat → Int) → Prop := fun _ _ => True

/-- One run: with `n` in cell 0 and the input after it, `P` halts within `t` steps with the right verdict and output. -/
def Problem.SolvedBy (Q : Problem) {n : Nat} (x : Q.Instance n) (P : List Instr) (W t : Nat) : Prop :=
  ∃ verdict m, exec P t 0 (loadWords W ((n : Int) :: Q.input x)) = some (verdict, m) ∧
    (verdict = true ↔ Q.yes x) ∧ Q.output x fun a => (m (1 + (Q.input x).length + a : Nat)).toInt

/-- Theorem 2: «a word RAM with O(log n)-bit words», «all numbers in the input are integers of absolute value
n^O(1)»: for every `κ`, one `P`, `b`, `T` for all instances, correct at every `W ≥ b(⌊log₂ n⌋ + 1)`. -/
def Problem.SolvedInTime (Q : Problem) (r : Rat) : Prop :=
  ∀ κ : Nat, ∃ (P : List Instr) (b : Nat) (T : Nat → Nat), BigO T r ∧
    ∀ (n : Nat) (x : Q.Instance n), (∀ a ∈ Q.input x, a.natAbs ≤ n ^ κ) → ∀ W ≥ b * (Nat.log2 n + 1),
      Q.SolvedBy x P W (T n)

def rowByRow {n : Nat} (w : Fin n → Fin n → Int) : List Int :=
  (List.ofFn fun u => List.ofFn fun v => w u v).flatten

/-- Section 3.2: «S(a, b, c) := w(a, b) + w(b, c) + w(a, c). A zero triangle is a triangle … with S(a, b, c) = 0». -/
def ExactTriangle : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (wAB, wBC, wAC) => rowByRow wAB ++ rowByRow wBC ++ rowByRow wAC
  yes := fun (wAB, wBC, wAC) => ∃ a b c, wAB a b + wBC b c + wAC a c = 0

/-- Theorem 19: «ε_T := 0.0017». -/
def ε_T : Rat := 0.0017

/-- Theorem 19: «Exact Triangle … can be solved by a deterministic algorithm in … O(n^(3−ε_T)) time». -/
def Theorem_19 : Prop :=
  ExactTriangle.SolvedInTime (3 - ε_T)

/-- Section 1: «Given n numbers, decide whether three of them sum to 0». Three different positions. -/
def ThreeSum : Problem where
  Instance n := Fin n → Int
  input x := List.ofFn x
  yes x := ∃ i j k, i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ x i + x j + x k = 0

/-- Theorem 22: «solve 3SUM on n integers of absolute value at most n^ν», in time «O(n^1.9992)». -/
def Theorem_22_3SUM : Prop :=
  ThreeSum.SolvedInTime 1.9992

/-- Output, row by row: entry `(i, j)` is the least of the sums `A i k + B k j`. -/
def MinPlusProduct : Problem where
  Instance n := (Fin n → Fin n → Int) × (Fin n → Fin n → Int)
  input := fun (A, B) => rowByRow A ++ rowByRow B
  output := fun {n} (A, B) out => ∀ i j : Fin n,
    (∃ k, out (i.val * n + j.val) = A i k + B k j) ∧ ∀ k, out (i.val * n + j.val) ≤ A i k + B k j

/-- Theorem 22: «the (min, +)-product of two n × n integer matrices», in time «O(n^2.99942)». -/
def Theorem_22_MinPlus : Prop :=
  MinPlusProduct.SolvedInTime 2.99942

/-- A path and its total weight; it may repeat vertices. -/
inductive Path {n : Nat} (w : Fin n → Fin n → Option Int) : Fin n → Fin n → Int → Prop
  | nil (i : Fin n) : Path w i i 0
  | cons {i j k : Fin n} {d e : Int} : w i j = some d → Path w j k e → Path w i k (d + e)

/-- Input: the 0/1 matrix of the edges, then the weights, with 0 for no edge. Output, two cells for each `(i, j)`: 1 if
there is a path, else 0; then the distance. -/
def APSP : Problem where
  Instance n := {w : Fin n → Fin n → Option Int // ∀ i d, Path w i i d → 0 ≤ d}
  input := fun ⟨w, _⟩ => rowByRow (fun i j => if (w i j).isSome then 1 else 0) ++ rowByRow fun i j => (w i j).getD 0
  output := fun {n} ⟨w, _⟩ out => ∀ i j : Fin n,
    let flag := out (2 * (i.val * n + j.val))
    let dist := out (2 * (i.val * n + j.val) + 1)
    (flag = 1 ∧ Path w i j dist ∧ ∀ e, Path w i j e → dist ≤ e) ∨ (flag = 0 ∧ ∀ e, ¬ Path w i j e)

/-- Theorem 22: «APSP on directed n-vertex graphs … and no negative cycles», in time «O(n^2.99942)». -/
def Theorem_22_APSP : Prop :=
  APSP.SolvedInTime 2.99942

/-- `w i j u v`: weight between `u` in part `i` and `v` in part `j`. All `k²` blocks are input; only `i < j` counts. -/
def ZeroWeightKClique (k : Nat) : Problem where
  Instance n := Fin k → Fin k → Fin n → Fin n → Int
  input w := (List.ofFn fun i => (List.ofFn fun j => rowByRow (w i j)).flatten).flatten
  yes {n} w := ∃ v : Fin k → Fin n,
    (List.ofFn fun j => (List.ofFn fun i => if i < j then w i j (v i) (v j) else 0).sum).sum = 0

/-- Corollary 39: «decide in O(n^(k−ε_T⌊k/3⌋)) time whether some k-clique … has total edge weight zero». -/
def Corollary_39_ZeroWeight : Prop :=
  ∀ k ≥ 3, (ZeroWeightKClique k).SolvedInTime (k - ε_T * (k / 3 : Nat))

end EndStatement

theorem ThreeSum1960614.integer_schedule (J s j : ℕ)
    (hJ : 0 < J) (hs : 0 < s) (heven : Even s) (hj : j < J)
    (hlevel : (j : ℝ) / J ≤ tau) :
    ∃ q : ℕ, 0 < q ∧ q ≤ ((J - j) * s) / 2 ∧ clearedSwitch J s j q ∧
      (∀ k < q, ¬ clearedSwitch J s j k) ∧
      threshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / ((J - j) * s)) ∧
      phi ((q : ℝ) / ((J - j) * s)) <
        threshold ((j : ℝ) / J) + 9 / ((J - j) * s) ∧
      saving ≤ 2 * beta - (j : ℝ) / J +
        (1 - (j : ℝ) / J) * gamma 232 ((q : ℝ) / ((J - j) * s)) ∧
      (1 - (j : ℝ) / J) * entropy ((q : ℝ) / ((J - j) * s)) <
        rho * (1 + v) + 9 * rho / (J * s) := by sorry