import Solutions.SnakyMilestones.Certificate35Block09Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_316_checked : entryAt 316 = entry_316 := by
  rw [entry_chunk_15 10 (by decide)]
  decide +kernel
theorem row_316 : rowAt 316 = data_316 := by
  rw [rowAt, dif_neg (by decide : ¬ 316 < 6), entry_316_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨306, 0, 5, 8⟩ (rowAt 306)] = data_316
  rw [row_6, row_306]
  apply row_ext <;> decide +kernel
theorem entry_good_316 : EntryGood 316 := by
  unfold EntryGood
  rw [entry_316_checked]
  decide +kernel
theorem good_316 : Good (rowAt 316) := by
  rw [row_316]
  unfold Good
  decide +kernel

theorem entry_317_checked : entryAt 317 = entry_317 := by
  rw [entry_chunk_15 11 (by decide)]
  decide +kernel
theorem row_317 : rowAt 317 = data_317 := by
  rw [rowAt, dif_neg (by decide : ¬ 317 < 6), entry_317_checked]
  change forkRow [placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨99, 0, 5, 5⟩ (rowAt 99)] = data_317
  rw [row_263, row_26, row_99]
  apply row_ext <;> decide +kernel
theorem entry_good_317 : EntryGood 317 := by
  unfold EntryGood
  rw [entry_317_checked]
  decide +kernel
theorem good_317 : Good (rowAt 317) := by
  rw [row_317]
  unfold Good
  decide +kernel

theorem entry_318_checked : entryAt 318 = entry_318 := by
  rw [entry_chunk_15 12 (by decide)]
  decide +kernel
theorem row_318 : rowAt 318 = data_318 := by
  rw [rowAt, dif_neg (by decide : ¬ 318 < 6), entry_318_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261), placeRow ⟨55, 1, 4, 5⟩ (rowAt 55)] = data_318
  rw [row_64, row_63, row_261, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_318 : EntryGood 318 := by
  unfold EntryGood
  rw [entry_318_checked]
  decide +kernel
theorem good_318 : Good (rowAt 318) := by
  rw [row_318]
  unfold Good
  decide +kernel

theorem entry_319_checked : entryAt 319 = entry_319 := by
  rw [entry_chunk_15 13 (by decide)]
  decide +kernel
theorem row_319 : rowAt 319 = data_319 := by
  rw [rowAt, dif_neg (by decide : ¬ 319 < 6), entry_319_checked]
  change forkRow [placeRow ⟨39, 2, 3, 4⟩ (rowAt 39), placeRow ⟨109, 4, 0, 5⟩ (rowAt 109), placeRow ⟨266, 1, 4, 5⟩ (rowAt 266), placeRow ⟨122, 4, 4, 5⟩ (rowAt 122)] = data_319
  rw [row_39, row_109, row_266, row_122]
  apply row_ext <;> decide +kernel
theorem entry_good_319 : EntryGood 319 := by
  unfold EntryGood
  rw [entry_319_checked]
  decide +kernel
theorem good_319 : Good (rowAt 319) := by
  rw [row_319]
  unfold Good
  decide +kernel


theorem block09_group03_piece01_correct : (rowAt 316 = data_316 ∧ Good (rowAt 316) ∧ EntryGood 316) ∧ (rowAt 317 = data_317 ∧ Good (rowAt 317) ∧ EntryGood 317) ∧ (rowAt 318 = data_318 ∧ Good (rowAt 318) ∧ EntryGood 318) ∧ (rowAt 319 = data_319 ∧ Good (rowAt 319) ∧ EntryGood 319) ∧ True := by
  exact ⟨⟨row_316, good_316, entry_good_316⟩, ⟨row_317, good_317, entry_good_317⟩, ⟨row_318, good_318, entry_good_318⟩, ⟨row_319, good_319, entry_good_319⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
