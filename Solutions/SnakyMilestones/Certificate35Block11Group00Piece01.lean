import Solutions.SnakyMilestones.Certificate35Block11Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_356_checked : entryAt 356 = entry_356 := by
  rw [entry_chunk_17 10 (by decide)]
  decide +kernel
theorem row_356 : rowAt 356 = data_356 := by
  rw [rowAt, dif_neg (by decide : ¬ 356 < 6), entry_356_checked]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨179, 0, 6, 4⟩ (rowAt 179)] = data_356
  rw [row_24, row_211, row_179]
  apply row_ext <;> decide +kernel
theorem entry_good_356 : EntryGood 356 := by
  unfold EntryGood
  rw [entry_356_checked]
  decide +kernel
theorem good_356 : Good (rowAt 356) := by
  rw [row_356]
  unfold Good
  decide +kernel

theorem entry_357_checked : entryAt 357 = entry_357 := by
  rw [entry_chunk_17 11 (by decide)]
  decide +kernel
theorem row_357 : rowAt 357 = data_357 := by
  rw [rowAt, dif_neg (by decide : ¬ 357 < 6), entry_357_checked]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (rowAt 82), placeRow ⟨283, 0, 5, 6⟩ (rowAt 283)] = data_357
  rw [row_82, row_283]
  apply row_ext <;> decide +kernel
theorem entry_good_357 : EntryGood 357 := by
  unfold EntryGood
  rw [entry_357_checked]
  decide +kernel
theorem good_357 : Good (rowAt 357) := by
  rw [row_357]
  unfold Good
  decide +kernel

theorem entry_358_checked : entryAt 358 = entry_358 := by
  rw [entry_chunk_17 12 (by decide)]
  decide +kernel
theorem row_358 : rowAt 358 = data_358 := by
  rw [rowAt, dif_neg (by decide : ¬ 358 < 6), entry_358_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨346, 0, 4, 6⟩ (rowAt 346)] = data_358
  rw [row_6, row_346]
  apply row_ext <;> decide +kernel
theorem entry_good_358 : EntryGood 358 := by
  unfold EntryGood
  rw [entry_358_checked]
  decide +kernel
theorem good_358 : Good (rowAt 358) := by
  rw [row_358]
  unfold Good
  decide +kernel

theorem entry_359_checked : entryAt 359 = entry_359 := by
  rw [entry_chunk_17 13 (by decide)]
  decide +kernel
theorem row_359 : rowAt 359 = data_359 := by
  rw [rowAt, dif_neg (by decide : ¬ 359 < 6), entry_359_checked]
  change forkRow [placeRow ⟨134, 0, 4, 6⟩ (rowAt 134), placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨323, 0, 5, 5⟩ (rowAt 323)] = data_359
  rw [row_134, row_24, row_323]
  apply row_ext <;> decide +kernel
theorem entry_good_359 : EntryGood 359 := by
  unfold EntryGood
  rw [entry_359_checked]
  decide +kernel
theorem good_359 : Good (rowAt 359) := by
  rw [row_359]
  unfold Good
  decide +kernel

theorem block11_group00_piece01_correct : (rowAt 356 = data_356 ∧ Good (rowAt 356) ∧ EntryGood 356) ∧ (rowAt 357 = data_357 ∧ Good (rowAt 357) ∧ EntryGood 357) ∧ (rowAt 358 = data_358 ∧ Good (rowAt 358) ∧ EntryGood 358) ∧ (rowAt 359 = data_359 ∧ Good (rowAt 359) ∧ EntryGood 359) ∧ True := by
  exact ⟨⟨row_356, good_356, entry_good_356⟩, ⟨row_357, good_357, entry_good_357⟩, ⟨row_358, good_358, entry_good_358⟩, ⟨row_359, good_359, entry_good_359⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
