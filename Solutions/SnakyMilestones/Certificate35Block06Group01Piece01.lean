import Solutions.SnakyMilestones.Certificate35Block06Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_204_checked : entryAt 204 = entry_204 := by
  rw [entry_chunk_9 18 (by decide)]
  decide +kernel
theorem row_204 : rowAt 204 = data_204 := by
  rw [rowAt, dif_neg (by decide : ¬ 204 < 6), entry_204_checked]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (rowAt 2), placeRow ⟨166, 2, 5, 3⟩ (rowAt 166)] = data_204
  rw [row_2, row_166]
  apply row_ext <;> decide +kernel
theorem entry_good_204 : EntryGood 204 := by
  unfold EntryGood
  rw [entry_204_checked]
  decide +kernel
theorem good_204 : Good (rowAt 204) := by
  rw [row_204]
  unfold Good
  decide +kernel

theorem entry_205_checked : entryAt 205 = entry_205 := by
  rw [entry_chunk_9 19 (by decide)]
  decide +kernel
theorem row_205 : rowAt 205 = data_205 := by
  rw [rowAt, dif_neg (by decide : ¬ 205 < 6), entry_205_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨168, 0, 3, 4⟩ (rowAt 168)] = data_205
  rw [row_4, row_168]
  apply row_ext <;> decide +kernel
theorem entry_good_205 : EntryGood 205 := by
  unfold EntryGood
  rw [entry_205_checked]
  decide +kernel
theorem good_205 : Good (rowAt 205) := by
  rw [row_205]
  unfold Good
  decide +kernel

theorem entry_206_checked : entryAt 206 = entry_206 := by
  rw [entry_chunk_10 0 (by decide)]
  decide +kernel
theorem row_206 : rowAt 206 = data_206 := by
  rw [rowAt, dif_neg (by decide : ¬ 206 < 6), entry_206_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨135, 2, 8, 4⟩ (rowAt 135)] = data_206
  rw [row_28, row_135]
  apply row_ext <;> decide +kernel
theorem entry_good_206 : EntryGood 206 := by
  unfold EntryGood
  rw [entry_206_checked]
  decide +kernel
theorem good_206 : Good (rowAt 206) := by
  rw [row_206]
  unfold Good
  decide +kernel

theorem entry_207_checked : entryAt 207 = entry_207 := by
  rw [entry_chunk_10 1 (by decide)]
  decide +kernel
theorem row_207 : rowAt 207 = data_207 := by
  rw [rowAt, dif_neg (by decide : ¬ 207 < 6), entry_207_checked]
  change forkRow [placeRow ⟨28, 3, 4, 5⟩ (rowAt 28), placeRow ⟨127, 0, 8, 4⟩ (rowAt 127)] = data_207
  rw [row_28, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_207 : EntryGood 207 := by
  unfold EntryGood
  rw [entry_207_checked]
  decide +kernel
theorem good_207 : Good (rowAt 207) := by
  rw [row_207]
  unfold Good
  decide +kernel

theorem block06_group01_piece01_correct : (rowAt 204 = data_204 ∧ Good (rowAt 204) ∧ EntryGood 204) ∧ (rowAt 205 = data_205 ∧ Good (rowAt 205) ∧ EntryGood 205) ∧ (rowAt 206 = data_206 ∧ Good (rowAt 206) ∧ EntryGood 206) ∧ (rowAt 207 = data_207 ∧ Good (rowAt 207) ∧ EntryGood 207) ∧ True := by
  exact ⟨⟨row_204, good_204, entry_good_204⟩, ⟨row_205, good_205, entry_good_205⟩, ⟨row_206, good_206, entry_good_206⟩, ⟨row_207, good_207, entry_good_207⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
