import Solutions.SnakyMilestones.Certificate35Block00Group03Piece02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_30_checked : entryAt 30 = entry_30 := by
  rw [entry_chunk_1 4 (by decide)]
  decide +kernel
theorem row_30 : rowAt 30 = data_30 := by
  rw [rowAt, dif_neg (by decide : ¬ 30 < 6), entry_30_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨14, 0, 6, 4⟩ (rowAt 14)] = data_30
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_30 : EntryGood 30 := by
  unfold EntryGood
  rw [entry_30_checked]
  decide +kernel
theorem good_30 : Good (rowAt 30) := by
  rw [row_30]
  unfold Good
  decide +kernel

theorem entry_31_checked : entryAt 31 = entry_31 := by
  rw [entry_chunk_1 5 (by decide)]
  decide +kernel
theorem row_31 : rowAt 31 = data_31 := by
  rw [rowAt, dif_neg (by decide : ¬ 31 < 6), entry_31_checked]
  change forkRow [placeRow ⟨0, 0, 1, 4⟩ (rowAt 0), placeRow ⟨17, 0, 6, 5⟩ (rowAt 17)] = data_31
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_31 : EntryGood 31 := by
  unfold EntryGood
  rw [entry_31_checked]
  decide +kernel
theorem good_31 : Good (rowAt 31) := by
  rw [row_31]
  unfold Good
  decide +kernel


theorem block00_group03_piece03_correct : (rowAt 30 = data_30 ∧ Good (rowAt 30) ∧ EntryGood 30) ∧ (rowAt 31 = data_31 ∧ Good (rowAt 31) ∧ EntryGood 31) ∧ True := by
  exact ⟨⟨row_30, good_30, entry_good_30⟩, ⟨row_31, good_31, entry_good_31⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
