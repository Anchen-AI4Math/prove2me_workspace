import Definitions.Def_Snaky35Cache09
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_15 (j : ℕ) (hj : j < 20) : entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_39 : rowAt 39 = data_39 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_99 : rowAt 99 = data_99 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.1).1
theorem row_109 : rowAt 109 = data_109 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_122 : rowAt 122 = data_122 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_148 : rowAt 148 = data_148 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_266 : rowAt 266 = data_266 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_272 : rowAt 272 = data_272 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_296 : rowAt 296 = data_296 := (OAI.SnakyCertificate.MilestoneChecks.block09_group01_correct.1).1
theorem row_305 : rowAt 305 = data_305 := (OAI.SnakyCertificate.MilestoneChecks.block09_group02_correct.2.1).1
theorem row_306 : rowAt 306 = data_306 := (OAI.SnakyCertificate.MilestoneChecks.block09_group02_correct.2.2.1).1
theorem entry_316_checked : entryAt 316 = entry_316 := by
  rw [entry_chunk_15 10 (by decide)]
  decide +kernel
theorem row_316 : rowAt 316 = data_316 := by
  rw [rowAt, dif_neg (by decide : ¬ 316 < 6), entry_316_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨306, 0, 5, 8⟩ (rowAt 306)] = data_316
  rw [row_6, row_306]
  apply row_ext <;> decide +kernel
theorem entry_good_316 : EntryGood 316 := by
  unfold EntryGood
  rw [entry_316_checked]
  decide +kernel
theorem good_316 : Good (rowAt 316) := by
  rw [row_316]
  unfold Good
  decide +kernel

theorem entry_317_checked : entryAt 317 = entry_317 := by
  rw [entry_chunk_15 11 (by decide)]
  decide +kernel
theorem row_317 : rowAt 317 = data_317 := by
  rw [rowAt, dif_neg (by decide : ¬ 317 < 6), entry_317_checked]
  change forkRow [placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨99, 0, 5, 5⟩ (rowAt 99)] = data_317
  rw [row_263, row_26, row_99]
  apply row_ext <;> decide +kernel
theorem entry_good_317 : EntryGood 317 := by
  unfold EntryGood
  rw [entry_317_checked]
  decide +kernel
theorem good_317 : Good (rowAt 317) := by
  rw [row_317]
  unfold Good
  decide +kernel

theorem entry_318_checked : entryAt 318 = entry_318 := by
  rw [entry_chunk_15 12 (by decide)]
  decide +kernel
theorem row_318 : rowAt 318 = data_318 := by
  rw [rowAt, dif_neg (by decide : ¬ 318 < 6), entry_318_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261), placeRow ⟨55, 1, 4, 5⟩ (rowAt 55)] = data_318
  rw [row_64, row_63, row_261, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_318 : EntryGood 318 := by
  unfold EntryGood
  rw [entry_318_checked]
  decide +kernel
theorem good_318 : Good (rowAt 318) := by
  rw [row_318]
  unfold Good
  decide +kernel

theorem entry_319_checked : entryAt 319 = entry_319 := by
  rw [entry_chunk_15 13 (by decide)]
  decide +kernel
theorem row_319 : rowAt 319 = data_319 := by
  rw [rowAt, dif_neg (by decide : ¬ 319 < 6), entry_319_checked]
  change forkRow [placeRow ⟨39, 2, 3, 4⟩ (rowAt 39), placeRow ⟨109, 4, 0, 5⟩ (rowAt 109), placeRow ⟨266, 1, 4, 5⟩ (rowAt 266), placeRow ⟨122, 4, 4, 5⟩ (rowAt 122)] = data_319
  rw [row_39, row_109, row_266, row_122]
  apply row_ext <;> decide +kernel
theorem entry_good_319 : EntryGood 319 := by
  unfold EntryGood
  rw [entry_319_checked]
  decide +kernel
theorem good_319 : Good (rowAt 319) := by
  rw [row_319]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 316 = data_316 ∧ Good (rowAt 316) ∧ EntryGood 316) ∧ (rowAt 317 = data_317 ∧ Good (rowAt 317) ∧ EntryGood 317) ∧ (rowAt 318 = data_318 ∧ Good (rowAt 318) ∧ EntryGood 318) ∧ (rowAt 319 = data_319 ∧ Good (rowAt 319) ∧ EntryGood 319) ∧ True := by
  exact ⟨⟨row_316, good_316, entry_good_316⟩, ⟨row_317, good_317, entry_good_317⟩, ⟨row_318, good_318, entry_good_318⟩, ⟨row_319, good_319, entry_good_319⟩, trivial⟩
