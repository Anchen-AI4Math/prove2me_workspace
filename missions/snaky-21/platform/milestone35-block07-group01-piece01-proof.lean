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
theorem entry_236_checked : entryAt 236 = entry_236 := by
  rw [entry_chunk_11 10 (by decide)]
  decide +kernel
theorem row_236 : rowAt 236 = data_236 := by
  rw [rowAt, dif_neg (by decide : ¬ 236 < 6), entry_236_checked]
  change forkRow [placeRow ⟨38, 1, 4, 5⟩ (rowAt 38), placeRow ⟨122, 7, 3, 4⟩ (rowAt 122), placeRow ⟨181, 0, 2, 3⟩ (rowAt 181), placeRow ⟨30, 1, 4, 3⟩ (rowAt 30)] = data_236
  rw [row_38, row_122, row_181, row_30]
  apply row_ext <;> decide +kernel
theorem entry_good_236 : EntryGood 236 := by
  unfold EntryGood
  rw [entry_236_checked]
  decide +kernel
theorem good_236 : Good (rowAt 236) := by
  rw [row_236]
  unfold Good
  decide +kernel

theorem entry_237_checked : entryAt 237 = entry_237 := by
  rw [entry_chunk_11 11 (by decide)]
  decide +kernel
theorem row_237 : rowAt 237 = data_237 := by
  rw [rowAt, dif_neg (by decide : ¬ 237 < 6), entry_237_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨172, 0, 7, 4⟩ (rowAt 172)] = data_237
  rw [row_6, row_172]
  apply row_ext <;> decide +kernel
theorem entry_good_237 : EntryGood 237 := by
  unfold EntryGood
  rw [entry_237_checked]
  decide +kernel
theorem good_237 : Good (rowAt 237) := by
  rw [row_237]
  unfold Good
  decide +kernel

theorem entry_238_checked : entryAt 238 = entry_238 := by
  rw [entry_chunk_11 12 (by decide)]
  decide +kernel
theorem row_238 : rowAt 238 = data_238 := by
  rw [rowAt, dif_neg (by decide : ¬ 238 < 6), entry_238_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨178, 5, 7, 4⟩ (rowAt 178)] = data_238
  rw [row_6, row_178]
  apply row_ext <;> decide +kernel
theorem entry_good_238 : EntryGood 238 := by
  unfold EntryGood
  rw [entry_238_checked]
  decide +kernel
theorem good_238 : Good (rowAt 238) := by
  rw [row_238]
  unfold Good
  decide +kernel

theorem entry_239_checked : entryAt 239 = entry_239 := by
  rw [entry_chunk_11 13 (by decide)]
  decide +kernel
theorem row_239 : rowAt 239 = data_239 := by
  rw [rowAt, dif_neg (by decide : ¬ 239 < 6), entry_239_checked]
  change forkRow [placeRow ⟨0, 4, 7, 3⟩ (rowAt 0), placeRow ⟨174, 4, 3, 5⟩ (rowAt 174)] = data_239
  rw [row_0, row_174]
  apply row_ext <;> decide +kernel
theorem entry_good_239 : EntryGood 239 := by
  unfold EntryGood
  rw [entry_239_checked]
  decide +kernel
theorem good_239 : Good (rowAt 239) := by
  rw [row_239]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 236 = data_236 ∧ Good (rowAt 236) ∧ EntryGood 236) ∧ (rowAt 237 = data_237 ∧ Good (rowAt 237) ∧ EntryGood 237) ∧ (rowAt 238 = data_238 ∧ Good (rowAt 238) ∧ EntryGood 238) ∧ (rowAt 239 = data_239 ∧ Good (rowAt 239) ∧ EntryGood 239) ∧ True := by
  exact ⟨⟨row_236, good_236, entry_good_236⟩, ⟨row_237, good_237, entry_good_237⟩, ⟨row_238, good_238, entry_good_238⟩, ⟨row_239, good_239, entry_good_239⟩, trivial⟩
