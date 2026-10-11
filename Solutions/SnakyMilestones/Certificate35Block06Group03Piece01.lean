import Solutions.SnakyMilestones.Certificate35Block06Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_220_checked : entryAt 220 = entry_220 := by
  rw [entry_chunk_10 14 (by decide)]
  decide +kernel
theorem row_220 : rowAt 220 = data_220 := by
  rw [rowAt, dif_neg (by decide : ¬ 220 < 6), entry_220_checked]
  change forkRow [placeRow ⟨56, 4, 0, 4⟩ (rowAt 56), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨144, 2, 5, 4⟩ (rowAt 144), placeRow ⟨154, 6, 5, 4⟩ (rowAt 154), placeRow ⟨155, 1, 5, 4⟩ (rowAt 155)] = data_220
  rw [row_56, row_63, row_144, row_154, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_220 : EntryGood 220 := by
  unfold EntryGood
  rw [entry_220_checked]
  decide +kernel
theorem good_220 : Good (rowAt 220) := by
  rw [row_220]
  unfold Good
  decide +kernel

theorem entry_221_checked : entryAt 221 = entry_221 := by
  rw [entry_chunk_10 15 (by decide)]
  decide +kernel
theorem row_221 : rowAt 221 = data_221 := by
  rw [rowAt, dif_neg (by decide : ¬ 221 < 6), entry_221_checked]
  change forkRow [placeRow ⟨6, 6, 0, 3⟩ (rowAt 6), placeRow ⟨180, 5, 5, 4⟩ (rowAt 180)] = data_221
  rw [row_6, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_221 : EntryGood 221 := by
  unfold EntryGood
  rw [entry_221_checked]
  decide +kernel
theorem good_221 : Good (rowAt 221) := by
  rw [row_221]
  unfold Good
  decide +kernel

theorem entry_222_checked : entryAt 222 = entry_222 := by
  rw [entry_chunk_10 16 (by decide)]
  decide +kernel
theorem row_222 : rowAt 222 = data_222 := by
  rw [rowAt, dif_neg (by decide : ¬ 222 < 6), entry_222_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨158, 5, 5, 4⟩ (rowAt 158)] = data_222
  rw [row_6, row_158]
  apply row_ext <;> decide +kernel
theorem entry_good_222 : EntryGood 222 := by
  unfold EntryGood
  rw [entry_222_checked]
  decide +kernel
theorem good_222 : Good (rowAt 222) := by
  rw [row_222]
  unfold Good
  decide +kernel

theorem entry_223_checked : entryAt 223 = entry_223 := by
  rw [entry_chunk_10 17 (by decide)]
  decide +kernel
theorem row_223 : rowAt 223 = data_223 := by
  rw [rowAt, dif_neg (by decide : ¬ 223 < 6), entry_223_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨135, 2, 5, 4⟩ (rowAt 135), placeRow ⟨128, 0, 3, 3⟩ (rowAt 128), placeRow ⟨111, 3, 4, 3⟩ (rowAt 111), placeRow ⟨127, 0, 5, 4⟩ (rowAt 127)] = data_223
  rw [row_63, row_135, row_128, row_111, row_127]
  apply row_ext <;> decide +kernel
theorem entry_good_223 : EntryGood 223 := by
  unfold EntryGood
  rw [entry_223_checked]
  decide +kernel
theorem good_223 : Good (rowAt 223) := by
  rw [row_223]
  unfold Good
  decide +kernel


theorem block06_group03_piece01_correct : (rowAt 220 = data_220 ∧ Good (rowAt 220) ∧ EntryGood 220) ∧ (rowAt 221 = data_221 ∧ Good (rowAt 221) ∧ EntryGood 221) ∧ (rowAt 222 = data_222 ∧ Good (rowAt 222) ∧ EntryGood 222) ∧ (rowAt 223 = data_223 ∧ Good (rowAt 223) ∧ EntryGood 223) ∧ True := by
  exact ⟨⟨row_220, good_220, entry_good_220⟩, ⟨row_221, good_221, entry_good_221⟩, ⟨row_222, good_222, entry_good_222⟩, ⟨row_223, good_223, entry_good_223⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
