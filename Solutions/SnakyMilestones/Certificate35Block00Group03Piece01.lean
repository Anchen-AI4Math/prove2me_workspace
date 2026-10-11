import Solutions.SnakyMilestones.Certificate35Block00Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_26_checked : entryAt 26 = entry_26 := by
  rw [entry_chunk_1 0 (by decide)]
  decide +kernel
theorem row_26 : rowAt 26 = data_26 := by
  rw [rowAt, dif_neg (by decide : ¬ 26 < 6), entry_26_checked]
  change forkRow [placeRow ⟨0, 4, 6, 4⟩ (rowAt 0), placeRow ⟨6, 0, 6, 5⟩ (rowAt 6)] = data_26
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_26 : EntryGood 26 := by
  unfold EntryGood
  rw [entry_26_checked]
  decide +kernel
theorem good_26 : Good (rowAt 26) := by
  rw [row_26]
  unfold Good
  decide +kernel

theorem entry_27_checked : entryAt 27 = entry_27 := by
  rw [entry_chunk_1 1 (by decide)]
  decide +kernel
theorem row_27 : rowAt 27 = data_27 := by
  rw [rowAt, dif_neg (by decide : ¬ 27 < 6), entry_27_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨6, 4, 0, 5⟩ (rowAt 6)] = data_27
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_27 : EntryGood 27 := by
  unfold EntryGood
  rw [entry_27_checked]
  decide +kernel
theorem good_27 : Good (rowAt 27) := by
  rw [row_27]
  unfold Good
  decide +kernel


theorem block00_group03_piece01_correct : (rowAt 26 = data_26 ∧ Good (rowAt 26) ∧ EntryGood 26) ∧ (rowAt 27 = data_27 ∧ Good (rowAt 27) ∧ EntryGood 27) ∧ True := by
  exact ⟨⟨row_26, good_26, entry_good_26⟩, ⟨row_27, good_27, entry_good_27⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
