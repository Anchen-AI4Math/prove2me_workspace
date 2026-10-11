import Solutions.SnakyMilestones.Certificate35Block02Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_92_checked : entryAt 92 = entry_92 := by
  rw [entry_chunk_4 6 (by decide)]
  decide +kernel
theorem row_92 : rowAt 92 = data_92 := by
  rw [rowAt, dif_neg (by decide : ¬ 92 < 6), entry_92_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨33, 0, 2, 3⟩ (rowAt 33)] = data_92
  rw [row_6, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_92 : EntryGood 92 := by
  unfold EntryGood
  rw [entry_92_checked]
  decide +kernel
theorem good_92 : Good (rowAt 92) := by
  rw [row_92]
  unfold Good
  decide +kernel

theorem entry_93_checked : entryAt 93 = entry_93 := by
  rw [entry_chunk_4 7 (by decide)]
  decide +kernel
theorem row_93 : rowAt 93 = data_93 := by
  rw [rowAt, dif_neg (by decide : ¬ 93 < 6), entry_93_checked]
  change forkRow [placeRow ⟨4, 3, 4, 3⟩ (rowAt 4), placeRow ⟨47, 0, 5, 4⟩ (rowAt 47)] = data_93
  rw [row_4, row_47]
  apply row_ext <;> decide +kernel
theorem entry_good_93 : EntryGood 93 := by
  unfold EntryGood
  rw [entry_93_checked]
  decide +kernel
theorem good_93 : Good (rowAt 93) := by
  rw [row_93]
  unfold Good
  decide +kernel

theorem entry_94_checked : entryAt 94 = entry_94 := by
  rw [entry_chunk_4 8 (by decide)]
  decide +kernel
theorem row_94 : rowAt 94 = data_94 := by
  rw [rowAt, dif_neg (by decide : ¬ 94 < 6), entry_94_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨27, 3, 3, 6⟩ (rowAt 27)] = data_94
  rw [row_6, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_94 : EntryGood 94 := by
  unfold EntryGood
  rw [entry_94_checked]
  decide +kernel
theorem good_94 : Good (rowAt 94) := by
  rw [row_94]
  unfold Good
  decide +kernel

theorem entry_95_checked : entryAt 95 = entry_95 := by
  rw [entry_chunk_4 9 (by decide)]
  decide +kernel
theorem row_95 : rowAt 95 = data_95 := by
  rw [rowAt, dif_neg (by decide : ¬ 95 < 6), entry_95_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨29, 0, 2, 5⟩ (rowAt 29)] = data_95
  rw [row_0, row_29]
  apply row_ext <;> decide +kernel
theorem entry_good_95 : EntryGood 95 := by
  unfold EntryGood
  rw [entry_95_checked]
  decide +kernel
theorem good_95 : Good (rowAt 95) := by
  rw [row_95]
  unfold Good
  decide +kernel


theorem block02_group03_piece01_correct : (rowAt 92 = data_92 ∧ Good (rowAt 92) ∧ EntryGood 92) ∧ (rowAt 93 = data_93 ∧ Good (rowAt 93) ∧ EntryGood 93) ∧ (rowAt 94 = data_94 ∧ Good (rowAt 94) ∧ EntryGood 94) ∧ (rowAt 95 = data_95 ∧ Good (rowAt 95) ∧ EntryGood 95) ∧ True := by
  exact ⟨⟨row_92, good_92, entry_good_92⟩, ⟨row_93, good_93, entry_good_93⟩, ⟨row_94, good_94, entry_good_94⟩, ⟨row_95, good_95, entry_good_95⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
