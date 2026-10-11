import Solutions.SnakyMilestones.Certificate35Block10Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_348_checked : entryAt 348 = entry_348 := by
  rw [entry_chunk_17 2 (by decide)]
  decide +kernel
theorem row_348 : rowAt 348 = data_348 := by
  rw [rowAt, dif_neg (by decide : ¬ 348 < 6), entry_348_checked]
  change forkRow [placeRow ⟨312, 1, 5, 5⟩ (rowAt 312), placeRow ⟨114, 4, 3, 4⟩ (rowAt 114), placeRow ⟨139, 3, 4, 5⟩ (rowAt 139)] = data_348
  rw [row_312, row_114, row_139]
  apply row_ext <;> decide +kernel
theorem entry_good_348 : EntryGood 348 := by
  unfold EntryGood
  rw [entry_348_checked]
  decide +kernel
theorem good_348 : Good (rowAt 348) := by
  rw [row_348]
  unfold Good
  decide +kernel

theorem entry_349_checked : entryAt 349 = entry_349 := by
  rw [entry_chunk_17 3 (by decide)]
  decide +kernel
theorem row_349 : rowAt 349 = data_349 := by
  rw [rowAt, dif_neg (by decide : ¬ 349 < 6), entry_349_checked]
  change forkRow [placeRow ⟨14, 1, 4, 5⟩ (rowAt 14), placeRow ⟨17, 1, 4, 5⟩ (rowAt 17), placeRow ⟨332, 0, 3, 4⟩ (rowAt 332)] = data_349
  rw [row_14, row_17, row_332]
  apply row_ext <;> decide +kernel
theorem entry_good_349 : EntryGood 349 := by
  unfold EntryGood
  rw [entry_349_checked]
  decide +kernel
theorem good_349 : Good (rowAt 349) := by
  rw [row_349]
  unfold Good
  decide +kernel

theorem entry_350_checked : entryAt 350 = entry_350 := by
  rw [entry_chunk_17 4 (by decide)]
  decide +kernel
theorem row_350 : rowAt 350 = data_350 := by
  rw [rowAt, dif_neg (by decide : ¬ 350 < 6), entry_350_checked]
  change forkRow [placeRow ⟨24, 4, 2, 5⟩ (rowAt 24), placeRow ⟨107, 2, 6, 4⟩ (rowAt 107), placeRow ⟨271, 4, 5, 5⟩ (rowAt 271), placeRow ⟨215, 0, 5, 5⟩ (rowAt 215)] = data_350
  rw [row_24, row_107, row_271, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_350 : EntryGood 350 := by
  unfold EntryGood
  rw [entry_350_checked]
  decide +kernel
theorem good_350 : Good (rowAt 350) := by
  rw [row_350]
  unfold Good
  decide +kernel

theorem entry_351_checked : entryAt 351 = entry_351 := by
  rw [entry_chunk_17 5 (by decide)]
  decide +kernel
theorem row_351 : rowAt 351 = data_351 := by
  rw [rowAt, dif_neg (by decide : ¬ 351 < 6), entry_351_checked]
  change forkRow [placeRow ⟨163, 0, 5, 4⟩ (rowAt 163), placeRow ⟨287, 4, 1, 4⟩ (rowAt 287), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25)] = data_351
  rw [row_163, row_287, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_351 : EntryGood 351 := by
  unfold EntryGood
  rw [entry_351_checked]
  decide +kernel
theorem good_351 : Good (rowAt 351) := by
  rw [row_351]
  unfold Good
  decide +kernel


theorem block10_group03_piece01_correct : (rowAt 348 = data_348 ∧ Good (rowAt 348) ∧ EntryGood 348) ∧ (rowAt 349 = data_349 ∧ Good (rowAt 349) ∧ EntryGood 349) ∧ (rowAt 350 = data_350 ∧ Good (rowAt 350) ∧ EntryGood 350) ∧ (rowAt 351 = data_351 ∧ Good (rowAt 351) ∧ EntryGood 351) ∧ True := by
  exact ⟨⟨row_348, good_348, entry_good_348⟩, ⟨row_349, good_349, entry_good_349⟩, ⟨row_350, good_350, entry_good_350⟩, ⟨row_351, good_351, entry_good_351⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
