import Solutions.SnakyMilestones.Certificate35Block13Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_436_checked : entryAt 436 = entry_436 := by
  rw [entry_chunk_21 10 (by decide)]
  decide +kernel
theorem row_436 : rowAt 436 = data_436 := by
  rw [rowAt, dif_neg (by decide : ¬ 436 < 6), entry_436_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨60, 3, 4, 3⟩ (rowAt 60), placeRow ⟨274, 4, 4, 3⟩ (rowAt 274), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428)] = data_436
  rw [row_51, row_60, row_274, row_428]
  apply row_ext <;> decide +kernel
theorem entry_good_436 : EntryGood 436 := by
  unfold EntryGood
  rw [entry_436_checked]
  decide +kernel
theorem good_436 : Good (rowAt 436) := by
  rw [row_436]
  unfold Good
  decide +kernel

theorem entry_437_checked : entryAt 437 = entry_437 := by
  rw [entry_chunk_21 11 (by decide)]
  decide +kernel
theorem row_437 : rowAt 437 = data_437 := by
  rw [rowAt, dif_neg (by decide : ¬ 437 < 6), entry_437_checked]
  change forkRow [placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_437
  rw [row_55, row_427, row_63, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_437 : EntryGood 437 := by
  unfold EntryGood
  rw [entry_437_checked]
  decide +kernel
theorem good_437 : Good (rowAt 437) := by
  rw [row_437]
  unfold Good
  decide +kernel

theorem entry_438_checked : entryAt 438 = entry_438 := by
  rw [entry_chunk_21 12 (by decide)]
  decide +kernel
theorem row_438 : rowAt 438 = data_438 := by
  rw [rowAt, dif_neg (by decide : ¬ 438 < 6), entry_438_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨432, 0, 4, 6⟩ (rowAt 432)] = data_438
  rw [row_0, row_432]
  apply row_ext <;> decide +kernel
theorem entry_good_438 : EntryGood 438 := by
  unfold EntryGood
  rw [entry_438_checked]
  decide +kernel
theorem good_438 : Good (rowAt 438) := by
  rw [row_438]
  unfold Good
  decide +kernel

theorem entry_439_checked : entryAt 439 = entry_439 := by
  rw [entry_chunk_21 13 (by decide)]
  decide +kernel
theorem row_439 : rowAt 439 = data_439 := by
  rw [rowAt, dif_neg (by decide : ¬ 439 < 6), entry_439_checked]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨149, 0, 4, 3⟩ (rowAt 149)] = data_439
  rw [row_176, row_295, row_263, row_418, row_149]
  apply row_ext <;> decide +kernel
theorem entry_good_439 : EntryGood 439 := by
  unfold EntryGood
  rw [entry_439_checked]
  decide +kernel
theorem good_439 : Good (rowAt 439) := by
  rw [row_439]
  unfold Good
  decide +kernel

theorem block13_group02_piece01_correct : (rowAt 436 = data_436 ∧ Good (rowAt 436) ∧ EntryGood 436) ∧ (rowAt 437 = data_437 ∧ Good (rowAt 437) ∧ EntryGood 437) ∧ (rowAt 438 = data_438 ∧ Good (rowAt 438) ∧ EntryGood 438) ∧ (rowAt 439 = data_439 ∧ Good (rowAt 439) ∧ EntryGood 439) ∧ True := by
  exact ⟨⟨row_436, good_436, entry_good_436⟩, ⟨row_437, good_437, entry_good_437⟩, ⟨row_438, good_438, entry_good_438⟩, ⟨row_439, good_439, entry_good_439⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
