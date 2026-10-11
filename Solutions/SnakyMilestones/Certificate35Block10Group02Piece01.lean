import Solutions.SnakyMilestones.Certificate35Block10Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_340_checked : entryAt 340 = entry_340 := by
  rw [entry_chunk_16 14 (by decide)]
  decide +kernel
theorem row_340 : rowAt 340 = data_340 := by
  rw [rowAt, dif_neg (by decide : ¬ 340 < 6), entry_340_checked]
  change forkRow [placeRow ⟨25, 3, 3, 6⟩ (rowAt 25), placeRow ⟨300, 4, 4, 6⟩ (rowAt 300), placeRow ⟨24, 3, 3, 6⟩ (rowAt 24)] = data_340
  rw [row_25, row_300, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_340 : EntryGood 340 := by
  unfold EntryGood
  rw [entry_340_checked]
  decide +kernel
theorem good_340 : Good (rowAt 340) := by
  rw [row_340]
  unfold Good
  decide +kernel

theorem entry_341_checked : entryAt 341 = entry_341 := by
  rw [entry_chunk_16 15 (by decide)]
  decide +kernel
theorem row_341 : rowAt 341 = data_341 := by
  rw [rowAt, dif_neg (by decide : ¬ 341 < 6), entry_341_checked]
  change forkRow [placeRow ⟨162, 5, 5, 4⟩ (rowAt 162), placeRow ⟨259, 4, 4, 5⟩ (rowAt 259), placeRow ⟨208, 2, 5, 4⟩ (rowAt 208), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143)] = data_341
  rw [row_162, row_259, row_208, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_341 : EntryGood 341 := by
  unfold EntryGood
  rw [entry_341_checked]
  decide +kernel
theorem good_341 : Good (rowAt 341) := by
  rw [row_341]
  unfold Good
  decide +kernel

theorem entry_342_checked : entryAt 342 = entry_342 := by
  rw [entry_chunk_16 16 (by decide)]
  decide +kernel
theorem row_342 : rowAt 342 = data_342 := by
  rw [rowAt, dif_neg (by decide : ¬ 342 < 6), entry_342_checked]
  change forkRow [placeRow ⟨210, 0, 5, 2⟩ (rowAt 210), placeRow ⟨88, 1, 4, 3⟩ (rowAt 88), placeRow ⟨260, 4, 4, 3⟩ (rowAt 260), placeRow ⟨290, 0, 4, 3⟩ (rowAt 290)] = data_342
  rw [row_210, row_88, row_260, row_290]
  apply row_ext <;> decide +kernel
theorem entry_good_342 : EntryGood 342 := by
  unfold EntryGood
  rw [entry_342_checked]
  decide +kernel
theorem good_342 : Good (rowAt 342) := by
  rw [row_342]
  unfold Good
  decide +kernel

theorem entry_343_checked : entryAt 343 = entry_343 := by
  rw [entry_chunk_16 17 (by decide)]
  decide +kernel
theorem row_343 : rowAt 343 = data_343 := by
  rw [rowAt, dif_neg (by decide : ¬ 343 < 6), entry_343_checked]
  change forkRow [placeRow ⟨0, 5, 4, 5⟩ (rowAt 0), placeRow ⟨250, 0, 5, 4⟩ (rowAt 250)] = data_343
  rw [row_0, row_250]
  apply row_ext <;> decide +kernel
theorem entry_good_343 : EntryGood 343 := by
  unfold EntryGood
  rw [entry_343_checked]
  decide +kernel
theorem good_343 : Good (rowAt 343) := by
  rw [row_343]
  unfold Good
  decide +kernel

theorem block10_group02_piece01_correct : (rowAt 340 = data_340 ∧ Good (rowAt 340) ∧ EntryGood 340) ∧ (rowAt 341 = data_341 ∧ Good (rowAt 341) ∧ EntryGood 341) ∧ (rowAt 342 = data_342 ∧ Good (rowAt 342) ∧ EntryGood 342) ∧ (rowAt 343 = data_343 ∧ Good (rowAt 343) ∧ EntryGood 343) ∧ True := by
  exact ⟨⟨row_340, good_340, entry_good_340⟩, ⟨row_341, good_341, entry_good_341⟩, ⟨row_342, good_342, entry_good_342⟩, ⟨row_343, good_343, entry_good_343⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
