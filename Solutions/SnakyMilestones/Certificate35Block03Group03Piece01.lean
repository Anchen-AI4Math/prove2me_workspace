import Solutions.SnakyMilestones.Certificate35Block03Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_124_checked : entryAt 124 = entry_124 := by
  rw [entry_chunk_5 18 (by decide)]
  decide +kernel
theorem row_124 : rowAt 124 = data_124 := by
  rw [rowAt, dif_neg (by decide : ¬ 124 < 6), entry_124_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨31, 2, 5, 4⟩ (rowAt 31)] = data_124
  rw [row_6, row_31]
  apply row_ext <;> decide +kernel
theorem entry_good_124 : EntryGood 124 := by
  unfold EntryGood
  rw [entry_124_checked]
  decide +kernel
theorem good_124 : Good (rowAt 124) := by
  rw [row_124]
  unfold Good
  decide +kernel

theorem entry_125_checked : entryAt 125 = entry_125 := by
  rw [entry_chunk_5 19 (by decide)]
  decide +kernel
theorem row_125 : rowAt 125 = data_125 := by
  rw [rowAt, dif_neg (by decide : ¬ 125 < 6), entry_125_checked]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (rowAt 3), placeRow ⟨31, 2, 4, 5⟩ (rowAt 31)] = data_125
  rw [row_3, row_31]
  apply row_ext <;> decide +kernel
theorem entry_good_125 : EntryGood 125 := by
  unfold EntryGood
  rw [entry_125_checked]
  decide +kernel
theorem good_125 : Good (rowAt 125) := by
  rw [row_125]
  unfold Good
  decide +kernel

theorem entry_126_checked : entryAt 126 = entry_126 := by
  rw [entry_chunk_6 0 (by decide)]
  decide +kernel
theorem row_126 : rowAt 126 = data_126 := by
  rw [rowAt, dif_neg (by decide : ¬ 126 < 6), entry_126_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨46, 1, 5, 7⟩ (rowAt 46)] = data_126
  rw [row_6, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_126 : EntryGood 126 := by
  unfold EntryGood
  rw [entry_126_checked]
  decide +kernel
theorem good_126 : Good (rowAt 126) := by
  rw [row_126]
  unfold Good
  decide +kernel

theorem entry_127_checked : entryAt 127 = entry_127 := by
  rw [entry_chunk_6 1 (by decide)]
  decide +kernel
theorem row_127 : rowAt 127 = data_127 := by
  rw [rowAt, dif_neg (by decide : ¬ 127 < 6), entry_127_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨44, 2, 5, 4⟩ (rowAt 44)] = data_127
  rw [row_7, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_127 : EntryGood 127 := by
  unfold EntryGood
  rw [entry_127_checked]
  decide +kernel
theorem good_127 : Good (rowAt 127) := by
  rw [row_127]
  unfold Good
  decide +kernel


theorem block03_group03_piece01_correct : (rowAt 124 = data_124 ∧ Good (rowAt 124) ∧ EntryGood 124) ∧ (rowAt 125 = data_125 ∧ Good (rowAt 125) ∧ EntryGood 125) ∧ (rowAt 126 = data_126 ∧ Good (rowAt 126) ∧ EntryGood 126) ∧ (rowAt 127 = data_127 ∧ Good (rowAt 127) ∧ EntryGood 127) ∧ True := by
  exact ⟨⟨row_124, good_124, entry_good_124⟩, ⟨row_125, good_125, entry_good_125⟩, ⟨row_126, good_126, entry_good_126⟩, ⟨row_127, good_127, entry_good_127⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
