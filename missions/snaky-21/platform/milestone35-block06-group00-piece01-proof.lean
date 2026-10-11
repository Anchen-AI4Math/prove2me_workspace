import Definitions.Def_Snaky35Cache06
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_9 (j : ℕ) (hj : j < 20) : entryAt (186 + j) = tableChunk_9[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_84 : rowAt 84 = data_84 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_103 : rowAt 103 = data_103 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_146 : rowAt 146 = data_146 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_187 : rowAt 187 = data_187 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_196_checked : entryAt 196 = entry_196 := by
  rw [entry_chunk_9 10 (by decide)]
  decide +kernel
theorem row_196 : rowAt 196 = data_196 := by
  rw [rowAt, dif_neg (by decide : ¬ 196 < 6), entry_196_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨187, 5, 6, 4⟩ (rowAt 187)] = data_196
  rw [row_6, row_187]
  apply row_ext <;> decide +kernel
theorem entry_good_196 : EntryGood 196 := by
  unfold EntryGood
  rw [entry_196_checked]
  decide +kernel
theorem good_196 : Good (rowAt 196) := by
  rw [row_196]
  unfold Good
  decide +kernel

theorem entry_197_checked : entryAt 197 = entry_197 := by
  rw [entry_chunk_9 11 (by decide)]
  decide +kernel
theorem row_197 : rowAt 197 = data_197 := by
  rw [rowAt, dif_neg (by decide : ¬ 197 < 6), entry_197_checked]
  change forkRow [placeRow ⟨63, 3, 0, 3⟩ (rowAt 63), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63)] = data_197
  rw [row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_197 : EntryGood 197 := by
  unfold EntryGood
  rw [entry_197_checked]
  decide +kernel
theorem good_197 : Good (rowAt 197) := by
  rw [row_197]
  unfold Good
  decide +kernel

theorem entry_198_checked : entryAt 198 = entry_198 := by
  rw [entry_chunk_9 12 (by decide)]
  decide +kernel
theorem row_198 : rowAt 198 = data_198 := by
  rw [rowAt, dif_neg (by decide : ¬ 198 < 6), entry_198_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨131, 1, 5, 4⟩ (rowAt 131)] = data_198
  rw [row_7, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_198 : EntryGood 198 := by
  unfold EntryGood
  rw [entry_198_checked]
  decide +kernel
theorem good_198 : Good (rowAt 198) := by
  rw [row_198]
  unfold Good
  decide +kernel

theorem entry_199_checked : entryAt 199 = entry_199 := by
  rw [entry_chunk_9 13 (by decide)]
  decide +kernel
theorem row_199 : rowAt 199 = data_199 := by
  rw [rowAt, dif_neg (by decide : ¬ 199 < 6), entry_199_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨84, 0, 3, 4⟩ (rowAt 84)] = data_199
  rw [row_55, row_64, row_84]
  apply row_ext <;> decide +kernel
theorem entry_good_199 : EntryGood 199 := by
  unfold EntryGood
  rw [entry_199_checked]
  decide +kernel
theorem good_199 : Good (rowAt 199) := by
  rw [row_199]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 196 = data_196 ∧ Good (rowAt 196) ∧ EntryGood 196) ∧ (rowAt 197 = data_197 ∧ Good (rowAt 197) ∧ EntryGood 197) ∧ (rowAt 198 = data_198 ∧ Good (rowAt 198) ∧ EntryGood 198) ∧ (rowAt 199 = data_199 ∧ Good (rowAt 199) ∧ EntryGood 199) ∧ True := by
  exact ⟨⟨row_196, good_196, entry_good_196⟩, ⟨row_197, good_197, entry_good_197⟩, ⟨row_198, good_198, entry_good_198⟩, ⟨row_199, good_199, entry_good_199⟩, trivial⟩
