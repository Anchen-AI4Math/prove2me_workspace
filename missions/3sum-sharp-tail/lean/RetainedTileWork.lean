import Mathlib
import Definitions.Def_APSPSource_RemainingDefinitions

open ThreeSumApsp.Spec Light.Sec4

namespace ThreeSumSharpTail

/-- The exact number of boxes visited by the `fillList` rounds of one tile. -/
def tileBoxWork (L m t : ℕ) : ℕ :=
  ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum

private theorem sum_map_affine (xs : List ℕ) (f : ℕ → ℕ) (a b : ℕ) :
    (xs.map fun x => a + f x * b).sum = xs.length * a + (xs.map f).sum * b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      ring

/-- Expanding the published routine costs gives an exact count in terms of
the box lists actually traversed by `tile`. -/
theorem tTile_eq_boxWork (L m t : ℕ) :
    tTile L m t = 220 + (m - t + 1) * (30 * L + 150) +
      tileBoxWork L m t * (580 * L + 790) := by
  have hfill (e : ℕ) :
      tFillList L (starBoxes L m t e).length + 60 =
        (30 * L + 150) + (starBoxes L m t e).length * (580 * L + 790) := by
    simp [tFillList, tNineFirst, tFillStep, tFillRound, tStarFirst, tHorner,
      tSumTen, tLookup, tInsert, tNineNext]
    ring
  unfold tTile tileBoxWork
  simp_rw [hfill]
  rw [sum_map_affine]
  simp [List.length_range, tNewRoot]
  ring

/-- The exact `tile` step count is bounded by a linear function of its actual
box work. -/
theorem tTile_le_boxWork (L m t : ℕ) :
    tTile L m t ≤ 1500 * (L + 1) * (tileBoxWork L m t + m + 1) := by
  rw [tTile_eq_boxWork]
  have hlen : m - t + 1 ≤ m + 1 := by omega
  have hbox : tileBoxWork L m t ≤ tileBoxWork L m t + m + 1 := by omega
  have hconst : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
  have hbase :
      30 * L + 150 ≤ 150 * (L + 1) := by omega
  have hcoef :
      580 * L + 790 ≤ 790 * (L + 1) := by omega
  have hmid : (m - t + 1) * (30 * L + 150) ≤
      150 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    calc
      _ ≤ (m + 1) * (150 * (L + 1)) := Nat.mul_le_mul hlen hbase
      _ = 150 * (L + 1) * (m + 1) := by ring
      _ ≤ 150 * (L + 1) * (tileBoxWork L m t + m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
  have hwork : tileBoxWork L m t * (580 * L + 790) ≤
      790 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    calc
      _ ≤ tileBoxWork L m t * (790 * (L + 1)) :=
        Nat.mul_le_mul_left _ hcoef
      _ = 790 * (L + 1) * tileBoxWork L m t := by ring
      _ ≤ 790 * (L + 1) * (tileBoxWork L m t + m + 1) :=
        Nat.mul_le_mul_left _ (by omega)
  let P := (L + 1) * (tileBoxWork L m t + m + 1)
  have hmidP : (m - t + 1) * (30 * L + 150) ≤ 150 * P := by
    calc
      _ ≤ 150 * (L + 1) * (tileBoxWork L m t + m + 1) := hmid
      _ = 150 * P := by dsimp [P]; ring
  have hworkP : tileBoxWork L m t * (580 * L + 790) ≤ 790 * P := by
    calc
      _ ≤ 790 * (L + 1) * (tileBoxWork L m t + m + 1) := hwork
      _ = 790 * P := by dsimp [P]; ring
  have hconstP : 220 ≤ 220 * P := by
    dsimp [P]
    have hP : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) := hconst
    simpa using Nat.mul_le_mul_left 220 hP
  have hsum : 220 + (m - t + 1) * (30 * L + 150) +
      tileBoxWork L m t * (580 * L + 790) ≤ 220 * P + 150 * P + 790 * P := by
    calc
      _ = 220 + ((m - t + 1) * (30 * L + 150) +
          tileBoxWork L m t * (580 * L + 790)) := by omega
      _ ≤ 220 * P + (150 * P + 790 * P) :=
        Nat.add_le_add hconstP (Nat.add_le_add hmidP hworkP)
      _ = 220 * P + 150 * P + 790 * P := by omega
  calc
    _ ≤ 220 * P + 150 * P + 790 * P := hsum
    _ = 1160 * P := by ring
    _ ≤ 1500 * P := Nat.mul_le_mul_right P (by omega)
    _ = 1500 * (L + 1) * (tileBoxWork L m t + m + 1) := by ring

/-- Bound the exact cost of the actual all-tiles loop using the same retained
box work for each tile. -/
theorem tAllTiles_le_boxWork (L m t nB : ℕ) :
    tAllTiles L m t nB ≤
      1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1) + nB + 1) := by
  have htile := tTile_le_boxWork L m t
  have htile80 : tTile L m t + 80 ≤
      1580 * (L + 1) * (tileBoxWork L m t + m + 1) := by
    have hP : 1 ≤ (L + 1) * (tileBoxWork L m t + m + 1) :=
      Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
    nlinarith
  have hmain : nB * (nB * (tTile L m t + 80)) ≤
      1580 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1)) := by
    calc
      _ ≤ nB * (nB *
          (1580 * (L + 1) * (tileBoxWork L m t + m + 1))) :=
        Nat.mul_le_mul_left nB (Nat.mul_le_mul_left nB htile80)
      _ ≤ 1580 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := by ring_nf; omega
  have hmain' : nB * (nB * (tTile L m t + 80)) ≤
      1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1)) := by
    calc
      _ ≤ 1580 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := hmain
      _ ≤ 1600 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) := by
        exact Nat.mul_le_mul_right _ (by omega)
  have hover : 40 * nB + 30 ≤ 1600 * (L + 1) * (nB + 1) := by
    nlinarith [Nat.zero_le nB, Nat.zero_le L]
  rw [tAllTiles]
  calc
    nB * (nB * (tTile L m t + 80) + 40) + 30 =
        nB * (nB * (tTile L m t + 80)) + (40 * nB + 30) := by ring
    _ ≤ 1600 * (L + 1) *
          (nB * nB * (tileBoxWork L m t + m + 1)) +
        1600 * (L + 1) * (nB + 1) := Nat.add_le_add hmain' hover
    _ = 1600 * (L + 1) *
        (nB * nB * (tileBoxWork L m t + m + 1) + nB + 1) := by ring

#print axioms tTile_eq_boxWork
#print axioms tTile_le_boxWork
#print axioms tAllTiles_le_boxWork

end ThreeSumSharpTail
