import Definitions.Def_Snaky35Cache07
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
theorem entry_chunk_11 (j : ℕ) (hj : j < 20) : entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_30 : rowAt 30 = data_30 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_32 : rowAt 32 = data_32 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.1).1
theorem row_37 : rowAt 37 = data_37 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.1).1
theorem row_38 : rowAt 38 = data_38 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_70 : rowAt 70 = data_70 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_110 : rowAt 110 = data_110 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_122 : rowAt 122 = data_122 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_129 : rowAt 129 = data_129 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.1).1
theorem row_133 : rowAt 133 = data_133 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_174 : rowAt 174 = data_174 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_178 : rowAt 178 = data_178 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_181 : rowAt 181 = data_181 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
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


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 232 = data_232 ∧ Good (rowAt 232) ∧ EntryGood 232) ∧ (rowAt 233 = data_233 ∧ Good (rowAt 233) ∧ EntryGood 233) ∧ (rowAt 234 = data_234 ∧ Good (rowAt 234) ∧ EntryGood 234) ∧ (rowAt 235 = data_235 ∧ Good (rowAt 235) ∧ EntryGood 235) ∧ True := by
  exact ⟨⟨row_232, good_232, entry_good_232⟩, ⟨row_233, good_233, entry_good_233⟩, ⟨row_234, good_234, entry_good_234⟩, ⟨row_235, good_235, entry_good_235⟩, trivial⟩
