import Definitions.Def_Snaky35Cache07
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_10 (j : ℕ) (hj : j < 20) : entryAt (206 + j) = tableChunk_10[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_11 (j : ℕ) (hj : j < 20) : entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_10 : rowAt 10 = data_10 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_45 : rowAt 45 = data_45 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_61 : rowAt 61 = data_61 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_68 : rowAt 68 = data_68 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.1).1
theorem row_82 : rowAt 82 = data_82 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_111 : rowAt 111 = data_111 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_171 : rowAt 171 = data_171 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_193 : rowAt 193 = data_193 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.1).1
theorem row_203 : rowAt 203 = data_203 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_212 : rowAt 212 = data_212 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_222 : rowAt 222 = data_222 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_228_checked : entryAt 228 = entry_228 := by
  rw [entry_chunk_11 2 (by decide)]
  decide +kernel
theorem row_228 : rowAt 228 = data_228 := by
  rw [rowAt, dif_neg (by decide : ¬ 228 < 6), entry_228_checked]
  change forkRow [placeRow ⟨82, 0, 6, 5⟩ (rowAt 82), placeRow ⟨68, 3, 5, 7⟩ (rowAt 68)] = data_228
  rw [row_82, row_68]
  apply row_ext <;> decide +kernel
theorem entry_good_228 : EntryGood 228 := by
  unfold EntryGood
  rw [entry_228_checked]
  decide +kernel
theorem good_228 : Good (rowAt 228) := by
  rw [row_228]
  unfold Good
  decide +kernel

theorem entry_229_checked : entryAt 229 = entry_229 := by
  rw [entry_chunk_11 3 (by decide)]
  decide +kernel
theorem row_229 : rowAt 229 = data_229 := by
  rw [rowAt, dif_neg (by decide : ¬ 229 < 6), entry_229_checked]
  change forkRow [placeRow ⟨171, 0, 7, 3⟩ (rowAt 171), placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_229
  rw [row_171, row_45, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_229 : EntryGood 229 := by
  unfold EntryGood
  rw [entry_229_checked]
  decide +kernel
theorem good_229 : Good (rowAt 229) := by
  rw [row_229]
  unfold Good
  decide +kernel

theorem entry_230_checked : entryAt 230 = entry_230 := by
  rw [entry_chunk_11 4 (by decide)]
  decide +kernel
theorem row_230 : rowAt 230 = data_230 := by
  rw [rowAt, dif_neg (by decide : ¬ 230 < 6), entry_230_checked]
  change forkRow [placeRow ⟨10, 6, 3, 4⟩ (rowAt 10), placeRow ⟨193, 0, 5, 5⟩ (rowAt 193), placeRow ⟨203, 0, 8, 5⟩ (rowAt 203), placeRow ⟨33, 0, 5, 4⟩ (rowAt 33)] = data_230
  rw [row_10, row_193, row_203, row_33]
  apply row_ext <;> decide +kernel
theorem entry_good_230 : EntryGood 230 := by
  unfold EntryGood
  rw [entry_230_checked]
  decide +kernel
theorem good_230 : Good (rowAt 230) := by
  rw [row_230]
  unfold Good
  decide +kernel

theorem entry_231_checked : entryAt 231 = entry_231 := by
  rw [entry_chunk_11 5 (by decide)]
  decide +kernel
theorem row_231 : rowAt 231 = data_231 := by
  rw [rowAt, dif_neg (by decide : ¬ 231 < 6), entry_231_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨222, 0, 6, 4⟩ (rowAt 222)] = data_231
  rw [row_6, row_222]
  apply row_ext <;> decide +kernel
theorem entry_good_231 : EntryGood 231 := by
  unfold EntryGood
  rw [entry_231_checked]
  decide +kernel
theorem good_231 : Good (rowAt 231) := by
  rw [row_231]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 228 = data_228 ∧ Good (rowAt 228) ∧ EntryGood 228) ∧ (rowAt 229 = data_229 ∧ Good (rowAt 229) ∧ EntryGood 229) ∧ (rowAt 230 = data_230 ∧ Good (rowAt 230) ∧ EntryGood 230) ∧ (rowAt 231 = data_231 ∧ Good (rowAt 231) ∧ EntryGood 231) ∧ True := by
  exact ⟨⟨row_228, good_228, entry_good_228⟩, ⟨row_229, good_229, entry_good_229⟩, ⟨row_230, good_230, entry_good_230⟩, ⟨row_231, good_231, entry_good_231⟩, trivial⟩
