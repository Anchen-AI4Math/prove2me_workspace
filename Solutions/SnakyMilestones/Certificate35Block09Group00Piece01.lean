import Solutions.SnakyMilestones.Certificate35Block09Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_292_checked : entryAt 292 = entry_292 := by
  rw [entry_chunk_14 6 (by decide)]
  decide +kernel
theorem row_292 : rowAt 292 = data_292 := by
  rw [rowAt, dif_neg (by decide : ¬ 292 < 6), entry_292_checked]
  change forkRow [placeRow ⟨39, 0, 3, 4⟩ (rowAt 39), placeRow ⟨219, 3, 3, 4⟩ (rowAt 219), placeRow ⟨79, 1, 4, 3⟩ (rowAt 79)] = data_292
  rw [row_39, row_219, row_79]
  apply row_ext <;> decide +kernel
theorem entry_good_292 : EntryGood 292 := by
  unfold EntryGood
  rw [entry_292_checked]
  decide +kernel
theorem good_292 : Good (rowAt 292) := by
  rw [row_292]
  unfold Good
  decide +kernel

theorem entry_293_checked : entryAt 293 = entry_293 := by
  rw [entry_chunk_14 7 (by decide)]
  decide +kernel
theorem row_293 : rowAt 293 = data_293 := by
  rw [rowAt, dif_neg (by decide : ¬ 293 < 6), entry_293_checked]
  change forkRow [placeRow ⟨2, 7, 4, 3⟩ (rowAt 2), placeRow ⟨280, 0, 5, 4⟩ (rowAt 280)] = data_293
  rw [row_2, row_280]
  apply row_ext <;> decide +kernel
theorem entry_good_293 : EntryGood 293 := by
  unfold EntryGood
  rw [entry_293_checked]
  decide +kernel
theorem good_293 : Good (rowAt 293) := by
  rw [row_293]
  unfold Good
  decide +kernel

theorem entry_294_checked : entryAt 294 = entry_294 := by
  rw [entry_chunk_14 8 (by decide)]
  decide +kernel
theorem row_294 : rowAt 294 = data_294 := by
  rw [rowAt, dif_neg (by decide : ¬ 294 < 6), entry_294_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨196, 3, 1, 3⟩ (rowAt 196)] = data_294
  rw [row_63, row_196]
  apply row_ext <;> decide +kernel
theorem entry_good_294 : EntryGood 294 := by
  unfold EntryGood
  rw [entry_294_checked]
  decide +kernel
theorem good_294 : Good (rowAt 294) := by
  rw [row_294]
  unfold Good
  decide +kernel

theorem entry_295_checked : entryAt 295 = entry_295 := by
  rw [entry_chunk_14 9 (by decide)]
  decide +kernel
theorem row_295 : rowAt 295 = data_295 := by
  rw [rowAt, dif_neg (by decide : ¬ 295 < 6), entry_295_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨265, 4, 4, 3⟩ (rowAt 265)] = data_295
  rw [row_63, row_64, row_55, row_265]
  apply row_ext <;> decide +kernel
theorem entry_good_295 : EntryGood 295 := by
  unfold EntryGood
  rw [entry_295_checked]
  decide +kernel
theorem good_295 : Good (rowAt 295) := by
  rw [row_295]
  unfold Good
  decide +kernel

theorem block09_group00_piece01_correct : (rowAt 292 = data_292 ∧ Good (rowAt 292) ∧ EntryGood 292) ∧ (rowAt 293 = data_293 ∧ Good (rowAt 293) ∧ EntryGood 293) ∧ (rowAt 294 = data_294 ∧ Good (rowAt 294) ∧ EntryGood 294) ∧ (rowAt 295 = data_295 ∧ Good (rowAt 295) ∧ EntryGood 295) ∧ True := by
  exact ⟨⟨row_292, good_292, entry_good_292⟩, ⟨row_293, good_293, entry_good_293⟩, ⟨row_294, good_294, entry_good_294⟩, ⟨row_295, good_295, entry_good_295⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
