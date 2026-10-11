import Definitions.Def_Snaky35Cache07
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_11 (j : ℕ) (hj : j < 20) : entryAt (226 + j) = tableChunk_11[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_12 (j : ℕ) (hj : j < 20) : entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_11 : rowAt 11 = data_11 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_61 : rowAt 61 = data_61 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_99 : rowAt 99 = data_99 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_159 : rowAt 159 = data_159 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_186 : rowAt 186 = data_186 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_190 : rowAt 190 = data_190 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_229 : rowAt 229 = data_229 := (OAI.SnakyCertificate.MilestoneChecks.block07_group00_correct.2.2.2.2.2.1).1
theorem row_233 : rowAt 233 = data_233 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.1).1
theorem row_237 : rowAt 237 = data_237 := (OAI.SnakyCertificate.MilestoneChecks.block07_group01_correct.2.2.2.2.2.1).1
theorem entry_244_checked : entryAt 244 = entry_244 := by
  rw [entry_chunk_11 18 (by decide)]
  decide +kernel
theorem row_244 : rowAt 244 = data_244 := by
  rw [rowAt, dif_neg (by decide : ¬ 244 < 6), entry_244_checked]
  change forkRow [placeRow ⟨99, 4, 2, 5⟩ (rowAt 99), placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨11, 7, 3, 3⟩ (rowAt 11), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173)] = data_244
  rw [row_99, row_11, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_244 : EntryGood 244 := by
  unfold EntryGood
  rw [entry_244_checked]
  decide +kernel
theorem good_244 : Good (rowAt 244) := by
  rw [row_244]
  unfold Good
  decide +kernel

theorem entry_245_checked : entryAt 245 = entry_245 := by
  rw [entry_chunk_11 19 (by decide)]
  decide +kernel
theorem row_245 : rowAt 245 = data_245 := by
  rw [rowAt, dif_neg (by decide : ¬ 245 < 6), entry_245_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨175, 4, 0, 4⟩ (rowAt 175), placeRow ⟨143, 6, 4, 5⟩ (rowAt 143), placeRow ⟨186, 6, 0, 4⟩ (rowAt 186)] = data_245
  rw [row_64, row_175, row_143, row_186]
  apply row_ext <;> decide +kernel
theorem entry_good_245 : EntryGood 245 := by
  unfold EntryGood
  rw [entry_245_checked]
  decide +kernel
theorem good_245 : Good (rowAt 245) := by
  rw [row_245]
  unfold Good
  decide +kernel

theorem entry_246_checked : entryAt 246 = entry_246 := by
  rw [entry_chunk_12 0 (by decide)]
  decide +kernel
theorem row_246 : rowAt 246 = data_246 := by
  rw [rowAt, dif_neg (by decide : ¬ 246 < 6), entry_246_checked]
  change forkRow [placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨175, 2, 5, 4⟩ (rowAt 175), placeRow ⟨186, 0, 5, 4⟩ (rowAt 186), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143)] = data_246
  rw [row_64, row_175, row_186, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_246 : EntryGood 246 := by
  unfold EntryGood
  rw [entry_246_checked]
  decide +kernel
theorem good_246 : Good (rowAt 246) := by
  rw [row_246]
  unfold Good
  decide +kernel

theorem entry_247_checked : entryAt 247 = entry_247 := by
  rw [entry_chunk_12 1 (by decide)]
  decide +kernel
theorem row_247 : rowAt 247 = data_247 := by
  rw [rowAt, dif_neg (by decide : ¬ 247 < 6), entry_247_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨229, 0, 4, 5⟩ (rowAt 229)] = data_247
  rw [row_6, row_229]
  apply row_ext <;> decide +kernel
theorem entry_good_247 : EntryGood 247 := by
  unfold EntryGood
  rw [entry_247_checked]
  decide +kernel
theorem good_247 : Good (rowAt 247) := by
  rw [row_247]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 244 = data_244 ∧ Good (rowAt 244) ∧ EntryGood 244) ∧ (rowAt 245 = data_245 ∧ Good (rowAt 245) ∧ EntryGood 245) ∧ (rowAt 246 = data_246 ∧ Good (rowAt 246) ∧ EntryGood 246) ∧ (rowAt 247 = data_247 ∧ Good (rowAt 247) ∧ EntryGood 247) ∧ True := by
  exact ⟨⟨row_244, good_244, entry_good_244⟩, ⟨row_245, good_245, entry_good_245⟩, ⟨row_246, good_246, entry_good_246⟩, ⟨row_247, good_247, entry_good_247⟩, trivial⟩
