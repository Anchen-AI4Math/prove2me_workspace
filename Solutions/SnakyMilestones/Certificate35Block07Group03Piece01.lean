import Solutions.SnakyMilestones.Certificate35Block07Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_252_checked : entryAt 252 = entry_252 := by
  rw [entry_chunk_12 6 (by decide)]
  decide +kernel
theorem row_252 : rowAt 252 = data_252 := by
  rw [rowAt, dif_neg (by decide : ¬ 252 < 6), entry_252_checked]
  change forkRow [placeRow ⟨111, 3, 4, 3⟩ (rowAt 111), placeRow ⟨154, 6, 5, 4⟩ (rowAt 154), placeRow ⟨144, 2, 5, 4⟩ (rowAt 144), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨155, 1, 5, 4⟩ (rowAt 155)] = data_252
  rw [row_111, row_154, row_144, row_63, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_252 : EntryGood 252 := by
  unfold EntryGood
  rw [entry_252_checked]
  decide +kernel
theorem good_252 : Good (rowAt 252) := by
  rw [row_252]
  unfold Good
  decide +kernel

theorem entry_253_checked : entryAt 253 = entry_253 := by
  rw [entry_chunk_12 7 (by decide)]
  decide +kernel
theorem row_253 : rowAt 253 = data_253 := by
  rw [rowAt, dif_neg (by decide : ¬ 253 < 6), entry_253_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨177, 1, 6, 2⟩ (rowAt 177)] = data_253
  rw [row_29, row_177]
  apply row_ext <;> decide +kernel
theorem entry_good_253 : EntryGood 253 := by
  unfold EntryGood
  rw [entry_253_checked]
  decide +kernel
theorem good_253 : Good (rowAt 253) := by
  rw [row_253]
  unfold Good
  decide +kernel

theorem entry_254_checked : entryAt 254 = entry_254 := by
  rw [entry_chunk_12 8 (by decide)]
  decide +kernel
theorem row_254 : rowAt 254 = data_254 := by
  rw [rowAt, dif_neg (by decide : ¬ 254 < 6), entry_254_checked]
  change forkRow [placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨108, 0, 8, 5⟩ (rowAt 108)] = data_254
  rw [row_96, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_254 : EntryGood 254 := by
  unfold EntryGood
  rw [entry_254_checked]
  decide +kernel
theorem good_254 : Good (rowAt 254) := by
  rw [row_254]
  unfold Good
  decide +kernel

theorem entry_255_checked : entryAt 255 = entry_255 := by
  rw [entry_chunk_12 9 (by decide)]
  decide +kernel
theorem row_255 : rowAt 255 = data_255 := by
  rw [rowAt, dif_neg (by decide : ¬ 255 < 6), entry_255_checked]
  change forkRow [placeRow ⟨69, 0, 3, 3⟩ (rowAt 69), placeRow ⟨205, 0, 5, 5⟩ (rowAt 205), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7)] = data_255
  rw [row_69, row_205, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_255 : EntryGood 255 := by
  unfold EntryGood
  rw [entry_255_checked]
  decide +kernel
theorem good_255 : Good (rowAt 255) := by
  rw [row_255]
  unfold Good
  decide +kernel


theorem block07_group03_piece01_correct : (rowAt 252 = data_252 ∧ Good (rowAt 252) ∧ EntryGood 252) ∧ (rowAt 253 = data_253 ∧ Good (rowAt 253) ∧ EntryGood 253) ∧ (rowAt 254 = data_254 ∧ Good (rowAt 254) ∧ EntryGood 254) ∧ (rowAt 255 = data_255 ∧ Good (rowAt 255) ∧ EntryGood 255) ∧ True := by
  exact ⟨⟨row_252, good_252, entry_good_252⟩, ⟨row_253, good_253, entry_good_253⟩, ⟨row_254, good_254, entry_good_254⟩, ⟨row_255, good_255, entry_good_255⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
