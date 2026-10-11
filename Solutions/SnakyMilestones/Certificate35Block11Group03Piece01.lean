import Solutions.SnakyMilestones.Certificate35Block11Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_380_checked : entryAt 380 = entry_380 := by
  rw [entry_chunk_18 14 (by decide)]
  decide +kernel
theorem row_380 : rowAt 380 = data_380 := by
  rw [rowAt, dif_neg (by decide : ¬ 380 < 6), entry_380_checked]
  change forkRow [placeRow ⟨101, 4, 2, 5⟩ (rowAt 101), placeRow ⟨271, 0, 2, 5⟩ (rowAt 271), placeRow ⟨223, 0, 5, 4⟩ (rowAt 223), placeRow ⟨192, 3, 1, 4⟩ (rowAt 192)] = data_380
  rw [row_101, row_271, row_223, row_192]
  apply row_ext <;> decide +kernel
theorem entry_good_380 : EntryGood 380 := by
  unfold EntryGood
  rw [entry_380_checked]
  decide +kernel
theorem good_380 : Good (rowAt 380) := by
  rw [row_380]
  unfold Good
  decide +kernel

theorem entry_381_checked : entryAt 381 = entry_381 := by
  rw [entry_chunk_18 15 (by decide)]
  decide +kernel
theorem row_381 : rowAt 381 = data_381 := by
  rw [rowAt, dif_neg (by decide : ¬ 381 < 6), entry_381_checked]
  change forkRow [placeRow ⟨211, 6, 3, 4⟩ (rowAt 211), placeRow ⟨24, 0, 7, 5⟩ (rowAt 24), placeRow ⟨163, 4, 3, 4⟩ (rowAt 163), placeRow ⟨341, 0, 7, 4⟩ (rowAt 341)] = data_381
  rw [row_211, row_24, row_163, row_341]
  apply row_ext <;> decide +kernel
theorem entry_good_381 : EntryGood 381 := by
  unfold EntryGood
  rw [entry_381_checked]
  decide +kernel
theorem good_381 : Good (rowAt 381) := by
  rw [row_381]
  unfold Good
  decide +kernel

theorem entry_382_checked : entryAt 382 = entry_382 := by
  rw [entry_chunk_18 16 (by decide)]
  decide +kernel
theorem row_382 : rowAt 382 = data_382 := by
  rw [rowAt, dif_neg (by decide : ¬ 382 < 6), entry_382_checked]
  change forkRow [placeRow ⟨124, 1, 5, 3⟩ (rowAt 124), placeRow ⟨2, 7, 4, 3⟩ (rowAt 2)] = data_382
  rw [row_124, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_382 : EntryGood 382 := by
  unfold EntryGood
  rw [entry_382_checked]
  decide +kernel
theorem good_382 : Good (rowAt 382) := by
  rw [row_382]
  unfold Good
  decide +kernel

theorem entry_383_checked : entryAt 383 = entry_383 := by
  rw [entry_chunk_18 17 (by decide)]
  decide +kernel
theorem row_383 : rowAt 383 = data_383 := by
  rw [rowAt, dif_neg (by decide : ¬ 383 < 6), entry_383_checked]
  change forkRow [placeRow ⟨192, 3, 2, 4⟩ (rowAt 192), placeRow ⟨271, 0, 3, 5⟩ (rowAt 271), placeRow ⟨197, 0, 6, 4⟩ (rowAt 197), placeRow ⟨172, 0, 6, 4⟩ (rowAt 172), placeRow ⟨215, 4, 3, 5⟩ (rowAt 215)] = data_383
  rw [row_192, row_271, row_197, row_172, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_383 : EntryGood 383 := by
  unfold EntryGood
  rw [entry_383_checked]
  decide +kernel
theorem good_383 : Good (rowAt 383) := by
  rw [row_383]
  unfold Good
  decide +kernel


theorem block11_group03_piece01_correct : (rowAt 380 = data_380 ∧ Good (rowAt 380) ∧ EntryGood 380) ∧ (rowAt 381 = data_381 ∧ Good (rowAt 381) ∧ EntryGood 381) ∧ (rowAt 382 = data_382 ∧ Good (rowAt 382) ∧ EntryGood 382) ∧ (rowAt 383 = data_383 ∧ Good (rowAt 383) ∧ EntryGood 383) ∧ True := by
  exact ⟨⟨row_380, good_380, entry_good_380⟩, ⟨row_381, good_381, entry_good_381⟩, ⟨row_382, good_382, entry_good_382⟩, ⟨row_383, good_383, entry_good_383⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
