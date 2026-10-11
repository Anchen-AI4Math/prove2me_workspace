import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_13 (j : ℕ) (hj : j < 20) : entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_198 : rowAt 198 = data_198 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.1).1
theorem row_204 : rowAt 204 = data_204 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_234 : rowAt 234 = data_234 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_240 : rowAt 240 = data_240 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_249 : rowAt 249 = data_249 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_276_checked : entryAt 276 = entry_276 := by
  rw [entry_chunk_13 10 (by decide)]
  decide +kernel
theorem row_276 : rowAt 276 = data_276 := by
  rw [rowAt, dif_neg (by decide : ¬ 276 < 6), entry_276_checked]
  change forkRow [placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨177, 0, 5, 4⟩ (rowAt 177), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63)] = data_276
  rw [row_7, row_177, row_63]
  apply row_ext <;> decide +kernel
theorem entry_good_276 : EntryGood 276 := by
  unfold EntryGood
  rw [entry_276_checked]
  decide +kernel
theorem good_276 : Good (rowAt 276) := by
  rw [row_276]
  unfold Good
  decide +kernel

theorem entry_277_checked : entryAt 277 = entry_277 := by
  rw [entry_chunk_13 11 (by decide)]
  decide +kernel
theorem row_277 : rowAt 277 = data_277 := by
  rw [rowAt, dif_neg (by decide : ¬ 277 < 6), entry_277_checked]
  change forkRow [placeRow ⟨14, 3, 4, 5⟩ (rowAt 14), placeRow ⟨204, 2, 3, 0⟩ (rowAt 204), placeRow ⟨33, 1, 3, 2⟩ (rowAt 33)] = data_277
  rw [row_14, row_204, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_277 : EntryGood 277 := by
  unfold EntryGood
  rw [entry_277_checked]
  decide +kernel
theorem good_277 : Good (rowAt 277) := by
  rw [row_277]
  unfold Good
  decide +kernel

theorem entry_278_checked : entryAt 278 = entry_278 := by
  rw [entry_chunk_13 12 (by decide)]
  decide +kernel
theorem row_278 : rowAt 278 = data_278 := by
  rw [rowAt, dif_neg (by decide : ¬ 278 < 6), entry_278_checked]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨162, 1, 8, 4⟩ (rowAt 162)] = data_278
  rw [row_63, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_278 : EntryGood 278 := by
  unfold EntryGood
  rw [entry_278_checked]
  decide +kernel
theorem good_278 : Good (rowAt 278) := by
  rw [row_278]
  unfold Good
  decide +kernel

theorem entry_279_checked : entryAt 279 = entry_279 := by
  rw [entry_chunk_13 13 (by decide)]
  decide +kernel
theorem row_279 : rowAt 279 = data_279 := by
  rw [rowAt, dif_neg (by decide : ¬ 279 < 6), entry_279_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨234, 5, 7, 4⟩ (rowAt 234)] = data_279
  rw [row_6, row_234]
  apply row_ext <;> decide +kernel
theorem entry_good_279 : EntryGood 279 := by
  unfold EntryGood
  rw [entry_279_checked]
  decide +kernel
theorem good_279 : Good (rowAt 279) := by
  rw [row_279]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 276 = data_276 ∧ Good (rowAt 276) ∧ EntryGood 276) ∧ (rowAt 277 = data_277 ∧ Good (rowAt 277) ∧ EntryGood 277) ∧ (rowAt 278 = data_278 ∧ Good (rowAt 278) ∧ EntryGood 278) ∧ (rowAt 279 = data_279 ∧ Good (rowAt 279) ∧ EntryGood 279) ∧ True := by
  exact ⟨⟨row_276, good_276, entry_good_276⟩, ⟨row_277, good_277, entry_good_277⟩, ⟨row_278, good_278, entry_good_278⟩, ⟨row_279, good_279, entry_good_279⟩, trivial⟩
