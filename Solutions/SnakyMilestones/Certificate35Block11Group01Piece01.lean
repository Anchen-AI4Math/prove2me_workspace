import Solutions.SnakyMilestones.Certificate35Block11Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_364_checked : entryAt 364 = entry_364 := by
  rw [entry_chunk_17 18 (by decide)]
  decide +kernel
theorem row_364 : rowAt 364 = data_364 := by
  rw [rowAt, dif_neg (by decide : ¬ 364 < 6), entry_364_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨314, 2, 3, 1⟩ (rowAt 314)] = data_364
  rw [row_63, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_364 : EntryGood 364 := by
  unfold EntryGood
  rw [entry_364_checked]
  decide +kernel
theorem good_364 : Good (rowAt 364) := by
  rw [row_364]
  unfold Good
  decide +kernel

theorem entry_365_checked : entryAt 365 = entry_365 := by
  rw [entry_chunk_17 19 (by decide)]
  decide +kernel
theorem row_365 : rowAt 365 = data_365 := by
  rw [rowAt, dif_neg (by decide : ¬ 365 < 6), entry_365_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨354, 0, 4, 3⟩ (rowAt 354)] = data_365
  rw [row_6, row_354]
  apply row_ext <;> decide +kernel
theorem entry_good_365 : EntryGood 365 := by
  unfold EntryGood
  rw [entry_365_checked]
  decide +kernel
theorem good_365 : Good (rowAt 365) := by
  rw [row_365]
  unfold Good
  decide +kernel

theorem entry_366_checked : entryAt 366 = entry_366 := by
  rw [entry_chunk_18 0 (by decide)]
  decide +kernel
theorem row_366 : rowAt 366 = data_366 := by
  rw [rowAt, dif_neg (by decide : ¬ 366 < 6), entry_366_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨357, 0, 6, 2⟩ (rowAt 357)] = data_366
  rw [row_6, row_357]
  apply row_ext <;> decide +kernel
theorem entry_good_366 : EntryGood 366 := by
  unfold EntryGood
  rw [entry_366_checked]
  decide +kernel
theorem good_366 : Good (rowAt 366) := by
  rw [row_366]
  unfold Good
  decide +kernel

theorem entry_367_checked : entryAt 367 = entry_367 := by
  rw [entry_chunk_18 1 (by decide)]
  decide +kernel
theorem row_367 : rowAt 367 = data_367 := by
  rw [rowAt, dif_neg (by decide : ¬ 367 < 6), entry_367_checked]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (rowAt 6), placeRow ⟨361, 4, 4, 6⟩ (rowAt 361)] = data_367
  rw [row_6, row_361]
  apply row_ext <;> decide +kernel
theorem entry_good_367 : EntryGood 367 := by
  unfold EntryGood
  rw [entry_367_checked]
  decide +kernel
theorem good_367 : Good (rowAt 367) := by
  rw [row_367]
  unfold Good
  decide +kernel

theorem block11_group01_piece01_correct : (rowAt 364 = data_364 ∧ Good (rowAt 364) ∧ EntryGood 364) ∧ (rowAt 365 = data_365 ∧ Good (rowAt 365) ∧ EntryGood 365) ∧ (rowAt 366 = data_366 ∧ Good (rowAt 366) ∧ EntryGood 366) ∧ (rowAt 367 = data_367 ∧ Good (rowAt 367) ∧ EntryGood 367) ∧ True := by
  exact ⟨⟨row_364, good_364, entry_good_364⟩, ⟨row_365, good_365, entry_good_365⟩, ⟨row_366, good_366, entry_good_366⟩, ⟨row_367, good_367, entry_good_367⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
