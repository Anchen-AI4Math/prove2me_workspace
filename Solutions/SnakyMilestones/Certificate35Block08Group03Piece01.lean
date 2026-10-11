import Solutions.SnakyMilestones.Certificate35Block08Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_284_checked : entryAt 284 = entry_284 := by
  rw [entry_chunk_13 18 (by decide)]
  decide +kernel
theorem row_284 : rowAt 284 = data_284 := by
  rw [rowAt, dif_neg (by decide : ¬ 284 < 6), entry_284_checked]
  change forkRow [placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨224, 0, 5, 4⟩ (rowAt 224), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_284
  rw [row_45, row_224, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_284 : EntryGood 284 := by
  unfold EntryGood
  rw [entry_284_checked]
  decide +kernel
theorem good_284 : Good (rowAt 284) := by
  rw [row_284]
  unfold Good
  decide +kernel

theorem entry_285_checked : entryAt 285 = entry_285 := by
  rw [entry_chunk_13 19 (by decide)]
  decide +kernel
theorem row_285 : rowAt 285 = data_285 := by
  rw [rowAt, dif_neg (by decide : ¬ 285 < 6), entry_285_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨273, 0, 6, 4⟩ (rowAt 273)] = data_285
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_285 : EntryGood 285 := by
  unfold EntryGood
  rw [entry_285_checked]
  decide +kernel
theorem good_285 : Good (rowAt 285) := by
  rw [row_285]
  unfold Good
  decide +kernel

theorem entry_286_checked : entryAt 286 = entry_286 := by
  rw [entry_chunk_14 0 (by decide)]
  decide +kernel
theorem row_286 : rowAt 286 = data_286 := by
  rw [rowAt, dif_neg (by decide : ¬ 286 < 6), entry_286_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_286
  rw [row_6, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_286 : EntryGood 286 := by
  unfold EntryGood
  rw [entry_286_checked]
  decide +kernel
theorem good_286 : Good (rowAt 286) := by
  rw [row_286]
  unfold Good
  decide +kernel

theorem entry_287_checked : entryAt 287 = entry_287 := by
  rw [entry_chunk_14 1 (by decide)]
  decide +kernel
theorem row_287 : rowAt 287 = data_287 := by
  rw [rowAt, dif_neg (by decide : ¬ 287 < 6), entry_287_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨56, 0, 5, 4⟩ (rowAt 56), placeRow ⟨264, 4, 4, 5⟩ (rowAt 264)] = data_287
  rw [row_64, row_55, row_56, row_264]
  apply row_ext <;> decide +kernel
theorem entry_good_287 : EntryGood 287 := by
  unfold EntryGood
  rw [entry_287_checked]
  decide +kernel
theorem good_287 : Good (rowAt 287) := by
  rw [row_287]
  unfold Good
  decide +kernel


theorem block08_group03_piece01_correct : (rowAt 284 = data_284 ∧ Good (rowAt 284) ∧ EntryGood 284) ∧ (rowAt 285 = data_285 ∧ Good (rowAt 285) ∧ EntryGood 285) ∧ (rowAt 286 = data_286 ∧ Good (rowAt 286) ∧ EntryGood 286) ∧ (rowAt 287 = data_287 ∧ Good (rowAt 287) ∧ EntryGood 287) ∧ True := by
  exact ⟨⟨row_284, good_284, entry_good_284⟩, ⟨row_285, good_285, entry_good_285⟩, ⟨row_286, good_286, entry_good_286⟩, ⟨row_287, good_287, entry_good_287⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
