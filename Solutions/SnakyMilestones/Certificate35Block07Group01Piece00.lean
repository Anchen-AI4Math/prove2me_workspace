import Definitions.Def_Snaky35Cache07
import Solutions.SnakyMilestones.Certificate35Block07Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_232_checked : entryAt 232 = entry_232 := by
  rw [entry_chunk_11 6 (by decide)]
  decide +kernel
theorem row_232 : rowAt 232 = data_232 := by
  rw [rowAt, dif_neg (by decide : ¬ 232 < 6), entry_232_checked]
  change forkRow [placeRow ⟨24, 2, 5, 4⟩ (rowAt 24), placeRow ⟨107, 1, 4, 6⟩ (rowAt 107)] = data_232
  rw [row_24, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_232 : EntryGood 232 := by
  unfold EntryGood
  rw [entry_232_checked]
  decide +kernel
theorem good_232 : Good (rowAt 232) := by
  rw [row_232]
  unfold Good
  decide +kernel

theorem entry_233_checked : entryAt 233 = entry_233 := by
  rw [entry_chunk_11 7 (by decide)]
  decide +kernel
theorem row_233 : rowAt 233 = data_233 := by
  rw [rowAt, dif_neg (by decide : ¬ 233 < 6), entry_233_checked]
  change forkRow [placeRow ⟨32, 3, 3, 1⟩ (rowAt 32), placeRow ⟨133, 0, 6, 4⟩ (rowAt 133)] = data_233
  rw [row_32, row_133]
  apply row_ext <;> decide +kernel
theorem entry_good_233 : EntryGood 233 := by
  unfold EntryGood
  rw [entry_233_checked]
  decide +kernel
theorem good_233 : Good (rowAt 233) := by
  rw [row_233]
  unfold Good
  decide +kernel

theorem entry_234_checked : entryAt 234 = entry_234 := by
  rw [entry_chunk_11 8 (by decide)]
  decide +kernel
theorem row_234 : rowAt 234 = data_234 := by
  rw [rowAt, dif_neg (by decide : ¬ 234 < 6), entry_234_checked]
  change forkRow [placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨37, 0, 3, 4⟩ (rowAt 37), placeRow ⟨129, 0, 5, 3⟩ (rowAt 129), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63)] = data_234
  rw [row_180, row_37, row_129, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_234 : EntryGood 234 := by
  unfold EntryGood
  rw [entry_234_checked]
  decide +kernel
theorem good_234 : Good (rowAt 234) := by
  rw [row_234]
  unfold Good
  decide +kernel

theorem entry_235_checked : entryAt 235 = entry_235 := by
  rw [entry_chunk_11 9 (by decide)]
  decide +kernel
theorem row_235 : rowAt 235 = data_235 := by
  rw [rowAt, dif_neg (by decide : ¬ 235 < 6), entry_235_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨110, 0, 6, 4⟩ (rowAt 110), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70)] = data_235
  rw [row_7, row_110, row_70]
  apply row_ext <;> decide +kernel
theorem entry_good_235 : EntryGood 235 := by
  unfold EntryGood
  rw [entry_235_checked]
  decide +kernel
theorem good_235 : Good (rowAt 235) := by
  rw [row_235]
  unfold Good
  decide +kernel


theorem block07_group01_piece00_correct : (rowAt 232 = data_232 ∧ Good (rowAt 232) ∧ EntryGood 232) ∧ (rowAt 233 = data_233 ∧ Good (rowAt 233) ∧ EntryGood 233) ∧ (rowAt 234 = data_234 ∧ Good (rowAt 234) ∧ EntryGood 234) ∧ (rowAt 235 = data_235 ∧ Good (rowAt 235) ∧ EntryGood 235) ∧ True := by
  exact ⟨⟨row_232, good_232, entry_good_232⟩, ⟨row_233, good_233, entry_good_233⟩, ⟨row_234, good_234, entry_good_234⟩, ⟨row_235, good_235, entry_good_235⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
