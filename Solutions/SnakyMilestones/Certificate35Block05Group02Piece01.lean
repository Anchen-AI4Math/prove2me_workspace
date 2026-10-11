import Solutions.SnakyMilestones.Certificate35Block05Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_180_checked : entryAt 180 = entry_180 := by
  rw [entry_chunk_8 14 (by decide)]
  decide +kernel
theorem row_180 : rowAt 180 = data_180 := by
  rw [rowAt, dif_neg (by decide : ¬ 180 < 6), entry_180_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨155, 0, 4, 5⟩ (rowAt 155), placeRow ⟨132, 0, 3, 3⟩ (rowAt 132)] = data_180
  rw [row_7, row_63, row_155, row_132]
  apply row_ext <;> decide +kernel
theorem entry_good_180 : EntryGood 180 := by
  unfold EntryGood
  rw [entry_180_checked]
  decide +kernel
theorem good_180 : Good (rowAt 180) := by
  rw [row_180]
  unfold Good
  decide +kernel

theorem entry_181_checked : entryAt 181 = entry_181 := by
  rw [entry_chunk_8 15 (by decide)]
  decide +kernel
theorem row_181 : rowAt 181 = data_181 := by
  rw [rowAt, dif_neg (by decide : ¬ 181 < 6), entry_181_checked]
  change forkRow [placeRow ⟨24, 3, 4, 5⟩ (rowAt 24), placeRow ⟨87, 2, 6, 4⟩ (rowAt 87), placeRow ⟨90, 0, 7, 5⟩ (rowAt 90)] = data_181
  rw [row_24, row_87, row_90]
  apply row_ext <;> decide +kernel
theorem entry_good_181 : EntryGood 181 := by
  unfold EntryGood
  rw [entry_181_checked]
  decide +kernel
theorem good_181 : Good (rowAt 181) := by
  rw [row_181]
  unfold Good
  decide +kernel

theorem entry_182_checked : entryAt 182 = entry_182 := by
  rw [entry_chunk_8 16 (by decide)]
  decide +kernel
theorem row_182 : rowAt 182 = data_182 := by
  rw [rowAt, dif_neg (by decide : ¬ 182 < 6), entry_182_checked]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (rowAt 12), placeRow ⟨139, 0, 7, 4⟩ (rowAt 139)] = data_182
  rw [row_12, row_139]
  apply row_ext <;> decide +kernel
theorem entry_good_182 : EntryGood 182 := by
  unfold EntryGood
  rw [entry_182_checked]
  decide +kernel
theorem good_182 : Good (rowAt 182) := by
  rw [row_182]
  unfold Good
  decide +kernel

theorem entry_183_checked : entryAt 183 = entry_183 := by
  rw [entry_chunk_8 17 (by decide)]
  decide +kernel
theorem row_183 : rowAt 183 = data_183 := by
  rw [rowAt, dif_neg (by decide : ¬ 183 < 6), entry_183_checked]
  change forkRow [placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨63, 3, 0, 3⟩ (rowAt 63), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_183
  rw [row_64, row_63, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_183 : EntryGood 183 := by
  unfold EntryGood
  rw [entry_183_checked]
  decide +kernel
theorem good_183 : Good (rowAt 183) := by
  rw [row_183]
  unfold Good
  decide +kernel

theorem block05_group02_piece01_correct : (rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180) ∧ (rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181) ∧ (rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182) ∧ (rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183) ∧ True := by
  exact ⟨⟨row_180, good_180, entry_good_180⟩, ⟨row_181, good_181, entry_good_181⟩, ⟨row_182, good_182, entry_good_182⟩, ⟨row_183, good_183, entry_good_183⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
