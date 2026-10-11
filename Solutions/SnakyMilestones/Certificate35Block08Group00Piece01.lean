import Solutions.SnakyMilestones.Certificate35Block08Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_260_checked : entryAt 260 = entry_260 := by
  rw [entry_chunk_12 14 (by decide)]
  decide +kernel
theorem row_260 : rowAt 260 = data_260 := by
  rw [rowAt, dif_neg (by decide : ¬ 260 < 6), entry_260_checked]
  change forkRow [placeRow ⟨0, 5, 4, 6⟩ (rowAt 0), placeRow ⟨231, 0, 3, 5⟩ (rowAt 231)] = data_260
  rw [row_0, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_260 : EntryGood 260 := by
  unfold EntryGood
  rw [entry_260_checked]
  decide +kernel
theorem good_260 : Good (rowAt 260) := by
  rw [row_260]
  unfold Good
  decide +kernel

theorem entry_261_checked : entryAt 261 = entry_261 := by
  rw [entry_chunk_12 15 (by decide)]
  decide +kernel
theorem row_261 : rowAt 261 = data_261 := by
  rw [rowAt, dif_neg (by decide : ¬ 261 < 6), entry_261_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨242, 0, 6, 4⟩ (rowAt 242)] = data_261
  rw [row_6, row_242]
  apply row_ext <;> decide +kernel
theorem entry_good_261 : EntryGood 261 := by
  unfold EntryGood
  rw [entry_261_checked]
  decide +kernel
theorem good_261 : Good (rowAt 261) := by
  rw [row_261]
  unfold Good
  decide +kernel

theorem entry_262_checked : entryAt 262 = entry_262 := by
  rw [entry_chunk_12 16 (by decide)]
  decide +kernel
theorem row_262 : rowAt 262 = data_262 := by
  rw [rowAt, dif_neg (by decide : ¬ 262 < 6), entry_262_checked]
  change forkRow [placeRow ⟨0, 7, 5, 7⟩ (rowAt 0), placeRow ⟨213, 0, 3, 4⟩ (rowAt 213)] = data_262
  rw [row_0, row_213]
  apply row_ext <;> decide +kernel
theorem entry_good_262 : EntryGood 262 := by
  unfold EntryGood
  rw [entry_262_checked]
  decide +kernel
theorem good_262 : Good (rowAt 262) := by
  rw [row_262]
  unfold Good
  decide +kernel

theorem entry_263_checked : entryAt 263 = entry_263 := by
  rw [entry_chunk_12 17 (by decide)]
  decide +kernel
theorem row_263 : rowAt 263 = data_263 := by
  rw [rowAt, dif_neg (by decide : ¬ 263 < 6), entry_263_checked]
  change forkRow [placeRow ⟨144, 6, 0, 4⟩ (rowAt 144), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143), placeRow ⟨175, 0, 5, 4⟩ (rowAt 175), placeRow ⟨55, 6, 0, 4⟩ (rowAt 55)] = data_263
  rw [row_144, row_143, row_175, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_263 : EntryGood 263 := by
  unfold EntryGood
  rw [entry_263_checked]
  decide +kernel
theorem good_263 : Good (rowAt 263) := by
  rw [row_263]
  unfold Good
  decide +kernel

theorem block08_group00_piece01_correct : (rowAt 260 = data_260 ∧ Good (rowAt 260) ∧ EntryGood 260) ∧ (rowAt 261 = data_261 ∧ Good (rowAt 261) ∧ EntryGood 261) ∧ (rowAt 262 = data_262 ∧ Good (rowAt 262) ∧ EntryGood 262) ∧ (rowAt 263 = data_263 ∧ Good (rowAt 263) ∧ EntryGood 263) ∧ True := by
  exact ⟨⟨row_260, good_260, entry_good_260⟩, ⟨row_261, good_261, entry_good_261⟩, ⟨row_262, good_262, entry_good_262⟩, ⟨row_263, good_263, entry_good_263⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
