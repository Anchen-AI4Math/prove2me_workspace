import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_12 (j : ℕ) (hj : j < 20) : entryAt (246 + j) = tableChunk_12[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_13 (j : ℕ) (hj : j < 20) : entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_143 : rowAt 143 = data_143 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_175 : rowAt 175 = data_175 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_202 : rowAt 202 = data_202 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_242 : rowAt 242 = data_242 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_247 : rowAt 247 = data_247 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_250 : rowAt 250 = data_250 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_251 : rowAt 251 = data_251 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_264_checked : entryAt 264 = entry_264 := by
  rw [entry_chunk_12 18 (by decide)]
  decide +kernel
theorem row_264 : rowAt 264 = data_264 := by
  rw [rowAt, dif_neg (by decide : ¬ 264 < 6), entry_264_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨250, 1, 7, 4⟩ (rowAt 250)] = data_264
  rw [row_6, row_250]
  apply row_ext <;> decide +kernel
theorem entry_good_264 : EntryGood 264 := by
  unfold EntryGood
  rw [entry_264_checked]
  decide +kernel
theorem good_264 : Good (rowAt 264) := by
  rw [row_264]
  unfold Good
  decide +kernel

theorem entry_265_checked : entryAt 265 = entry_265 := by
  rw [entry_chunk_12 19 (by decide)]
  decide +kernel
theorem row_265 : rowAt 265 = data_265 := by
  rw [rowAt, dif_neg (by decide : ¬ 265 < 6), entry_265_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨247, 0, 4, 6⟩ (rowAt 247)] = data_265
  rw [row_6, row_247]
  apply row_ext <;> decide +kernel
theorem entry_good_265 : EntryGood 265 := by
  unfold EntryGood
  rw [entry_265_checked]
  decide +kernel
theorem good_265 : Good (rowAt 265) := by
  rw [row_265]
  unfold Good
  decide +kernel

theorem entry_266_checked : entryAt 266 = entry_266 := by
  rw [entry_chunk_13 0 (by decide)]
  decide +kernel
theorem row_266 : rowAt 266 = data_266 := by
  rw [rowAt, dif_neg (by decide : ¬ 266 < 6), entry_266_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨242, 0, 5, 4⟩ (rowAt 242)] = data_266
  rw [row_6, row_242]
  apply row_ext <;> decide +kernel
theorem entry_good_266 : EntryGood 266 := by
  unfold EntryGood
  rw [entry_266_checked]
  decide +kernel
theorem good_266 : Good (rowAt 266) := by
  rw [row_266]
  unfold Good
  decide +kernel

theorem entry_267_checked : entryAt 267 = entry_267 := by
  rw [entry_chunk_13 1 (by decide)]
  decide +kernel
theorem row_267 : rowAt 267 = data_267 := by
  rw [rowAt, dif_neg (by decide : ¬ 267 < 6), entry_267_checked]
  change forkRow [placeRow ⟨175, 4, 1, 4⟩ (rowAt 175), placeRow ⟨144, 2, 6, 4⟩ (rowAt 144), placeRow ⟨55, 2, 6, 4⟩ (rowAt 55), placeRow ⟨143, 4, 5, 3⟩ (rowAt 143)] = data_267
  rw [row_175, row_144, row_55, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_267 : EntryGood 267 := by
  unfold EntryGood
  rw [entry_267_checked]
  decide +kernel
theorem good_267 : Good (rowAt 267) := by
  rw [row_267]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 264 = data_264 ∧ Good (rowAt 264) ∧ EntryGood 264) ∧ (rowAt 265 = data_265 ∧ Good (rowAt 265) ∧ EntryGood 265) ∧ (rowAt 266 = data_266 ∧ Good (rowAt 266) ∧ EntryGood 266) ∧ (rowAt 267 = data_267 ∧ Good (rowAt 267) ∧ EntryGood 267) ∧ True := by
  exact ⟨⟨row_264, good_264, entry_good_264⟩, ⟨row_265, good_265, entry_good_265⟩, ⟨row_266, good_266, entry_good_266⟩, ⟨row_267, good_267, entry_good_267⟩, trivial⟩
