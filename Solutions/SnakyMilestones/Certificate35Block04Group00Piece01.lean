import Solutions.SnakyMilestones.Certificate35Block04Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_132_checked : entryAt 132 = entry_132 := by
  rw [entry_chunk_6 6 (by decide)]
  decide +kernel
theorem row_132 : rowAt 132 = data_132 := by
  rw [rowAt, dif_neg (by decide : ¬ 132 < 6), entry_132_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨89, 0, 5, 6⟩ (rowAt 89)] = data_132
  rw [row_6, row_89]
  apply row_ext <;> decide +kernel
theorem entry_good_132 : EntryGood 132 := by
  unfold EntryGood
  rw [entry_132_checked]
  decide +kernel
theorem good_132 : Good (rowAt 132) := by
  rw [row_132]
  unfold Good
  decide +kernel

theorem entry_133_checked : entryAt 133 = entry_133 := by
  rw [entry_chunk_6 7 (by decide)]
  decide +kernel
theorem row_133 : rowAt 133 = data_133 := by
  rw [rowAt, dif_neg (by decide : ¬ 133 < 6), entry_133_checked]
  change forkRow [placeRow ⟨6, 7, 3, 1⟩ (rowAt 6), placeRow ⟨92, 0, 5, 5⟩ (rowAt 92)] = data_133
  rw [row_6, row_92]
  apply row_ext <;> decide +kernel
theorem entry_good_133 : EntryGood 133 := by
  unfold EntryGood
  rw [entry_133_checked]
  decide +kernel
theorem good_133 : Good (rowAt 133) := by
  rw [row_133]
  unfold Good
  decide +kernel

theorem entry_134_checked : entryAt 134 = entry_134 := by
  rw [entry_chunk_6 8 (by decide)]
  decide +kernel
theorem row_134 : rowAt 134 = data_134 := by
  rw [rowAt, dif_neg (by decide : ¬ 134 < 6), entry_134_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨82, 0, 5, 4⟩ (rowAt 82)] = data_134
  rw [row_6, row_82]
  apply row_ext <;> decide +kernel
theorem entry_good_134 : EntryGood 134 := by
  unfold EntryGood
  rw [entry_134_checked]
  decide +kernel
theorem good_134 : Good (rowAt 134) := by
  rw [row_134]
  unfold Good
  decide +kernel

theorem entry_135_checked : entryAt 135 = entry_135 := by
  rw [entry_chunk_6 9 (by decide)]
  decide +kernel
theorem row_135 : rowAt 135 = data_135 := by
  rw [rowAt, dif_neg (by decide : ¬ 135 < 6), entry_135_checked]
  change forkRow [placeRow ⟨7, 0, 4, 5⟩ (rowAt 7), placeRow ⟨75, 4, 2, 5⟩ (rowAt 75), placeRow ⟨44, 0, 5, 4⟩ (rowAt 44)] = data_135
  rw [row_7, row_75, row_44]
  apply row_ext <;> decide +kernel
theorem entry_good_135 : EntryGood 135 := by
  unfold EntryGood
  rw [entry_135_checked]
  decide +kernel
theorem good_135 : Good (rowAt 135) := by
  rw [row_135]
  unfold Good
  decide +kernel

theorem block04_group00_piece01_correct : (rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132) ∧ (rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133) ∧ (rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134) ∧ (rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135) ∧ True := by
  exact ⟨⟨row_132, good_132, entry_good_132⟩, ⟨row_133, good_133, entry_good_133⟩, ⟨row_134, good_134, entry_good_134⟩, ⟨row_135, good_135, entry_good_135⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
