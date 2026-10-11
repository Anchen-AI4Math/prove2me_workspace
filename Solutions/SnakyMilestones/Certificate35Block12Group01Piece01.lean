import Solutions.SnakyMilestones.Certificate35Block12Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_396_checked : entryAt 396 = entry_396 := by
  rw [entry_chunk_19 10 (by decide)]
  decide +kernel
theorem row_396 : rowAt 396 = data_396 := by
  rw [rowAt, dif_neg (by decide : ¬ 396 < 6), entry_396_checked]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨365, 1, 7, 3⟩ (rowAt 365), placeRow ⟨303, 0, 4, 5⟩ (rowAt 303), placeRow ⟨65, 3, 4, 5⟩ (rowAt 65)] = data_396
  rw [row_107, row_365, row_303, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_396 : EntryGood 396 := by
  unfold EntryGood
  rw [entry_396_checked]
  decide +kernel
theorem good_396 : Good (rowAt 396) := by
  rw [row_396]
  unfold Good
  decide +kernel

theorem entry_397_checked : entryAt 397 = entry_397 := by
  rw [entry_chunk_19 11 (by decide)]
  decide +kernel
theorem row_397 : rowAt 397 = data_397 := by
  rw [rowAt, dif_neg (by decide : ¬ 397 < 6), entry_397_checked]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (rowAt 24), placeRow ⟨374, 0, 3, 4⟩ (rowAt 374), placeRow ⟨65, 5, 5, 1⟩ (rowAt 65)] = data_397
  rw [row_24, row_374, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_397 : EntryGood 397 := by
  unfold EntryGood
  rw [entry_397_checked]
  decide +kernel
theorem good_397 : Good (rowAt 397) := by
  rw [row_397]
  unfold Good
  decide +kernel

theorem entry_398_checked : entryAt 398 = entry_398 := by
  rw [entry_chunk_19 12 (by decide)]
  decide +kernel
theorem row_398 : rowAt 398 = data_398 := by
  rw [rowAt, dif_neg (by decide : ¬ 398 < 6), entry_398_checked]
  change forkRow [placeRow ⟨257, 0, 1, 3⟩ (rowAt 257), placeRow ⟨363, 0, 5, 4⟩ (rowAt 363), placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨177, 1, 4, 2⟩ (rowAt 177)] = data_398
  rw [row_257, row_363, row_130, row_177]
  apply row_ext <;> decide +kernel
theorem entry_good_398 : EntryGood 398 := by
  unfold EntryGood
  rw [entry_398_checked]
  decide +kernel
theorem good_398 : Good (rowAt 398) := by
  rw [row_398]
  unfold Good
  decide +kernel

theorem entry_399_checked : entryAt 399 = entry_399 := by
  rw [entry_chunk_19 13 (by decide)]
  decide +kernel
theorem row_399 : rowAt 399 = data_399 := by
  rw [rowAt, dif_neg (by decide : ¬ 399 < 6), entry_399_checked]
  change forkRow [placeRow ⟨192, 6, 4, 1⟩ (rowAt 192), placeRow ⟨271, 3, 3, 2⟩ (rowAt 271), placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319), placeRow ⟨215, 7, 3, 2⟩ (rowAt 215)] = data_399
  rw [row_192, row_271, row_173, row_319, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_399 : EntryGood 399 := by
  unfold EntryGood
  rw [entry_399_checked]
  decide +kernel
theorem good_399 : Good (rowAt 399) := by
  rw [row_399]
  unfold Good
  decide +kernel

theorem block12_group01_piece01_correct : (rowAt 396 = data_396 ∧ Good (rowAt 396) ∧ EntryGood 396) ∧ (rowAt 397 = data_397 ∧ Good (rowAt 397) ∧ EntryGood 397) ∧ (rowAt 398 = data_398 ∧ Good (rowAt 398) ∧ EntryGood 398) ∧ (rowAt 399 = data_399 ∧ Good (rowAt 399) ∧ EntryGood 399) ∧ True := by
  exact ⟨⟨row_396, good_396, entry_good_396⟩, ⟨row_397, good_397, entry_good_397⟩, ⟨row_398, good_398, entry_good_398⟩, ⟨row_399, good_399, entry_good_399⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
