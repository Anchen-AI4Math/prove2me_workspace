import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_17 (j : ℕ) (hj : j < 20) : entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_17 : rowAt 17 = data_17 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_60 : rowAt 60 = data_60 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_114 : rowAt 114 = data_114 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_139 : rowAt 139 = data_139 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_255 : rowAt 255 = data_255 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_262 : rowAt 262 = data_262 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_276 : rowAt 276 = data_276 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_287 : rowAt 287 = data_287 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_312 : rowAt 312 = data_312 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_320 : rowAt 320 = data_320 := (OAI.SnakyCertificate.MilestoneChecks.block10_group00_correct.1).1
theorem row_332 : rowAt 332 = data_332 := (OAI.SnakyCertificate.MilestoneChecks.block10_group01_correct.2.2.2.2.1).1
theorem row_339 : rowAt 339 = data_339 := (OAI.SnakyCertificate.MilestoneChecks.block10_group02_correct.2.2.2.1).1
theorem entry_344_checked : entryAt 344 = entry_344 := by
  rw [entry_chunk_16 18 (by decide)]
  decide +kernel
theorem row_344 : rowAt 344 = data_344 := by
  rw [rowAt, dif_neg (by decide : ¬ 344 < 6), entry_344_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108), placeRow ⟨262, 4, 5, 2⟩ (rowAt 262)] = data_344
  rw [row_7, row_108, row_262]
  apply row_ext <;> decide +kernel
theorem entry_good_344 : EntryGood 344 := by
  unfold EntryGood
  rw [entry_344_checked]
  decide +kernel
theorem good_344 : Good (rowAt 344) := by
  rw [row_344]
  unfold Good
  decide +kernel

theorem entry_345_checked : entryAt 345 = entry_345 := by
  rw [entry_chunk_16 19 (by decide)]
  decide +kernel
theorem row_345 : rowAt 345 = data_345 := by
  rw [rowAt, dif_neg (by decide : ¬ 345 < 6), entry_345_checked]
  change forkRow [placeRow ⟨6, 0, 5, 5⟩ (rowAt 6), placeRow ⟨320, 4, 4, 7⟩ (rowAt 320)] = data_345
  rw [row_6, row_320]
  apply row_ext <;> decide +kernel
theorem entry_good_345 : EntryGood 345 := by
  unfold EntryGood
  rw [entry_345_checked]
  decide +kernel
theorem good_345 : Good (rowAt 345) := by
  rw [row_345]
  unfold Good
  decide +kernel

theorem entry_346_checked : entryAt 346 = entry_346 := by
  rw [entry_chunk_17 0 (by decide)]
  decide +kernel
theorem row_346 : rowAt 346 = data_346 := by
  rw [rowAt, dif_neg (by decide : ¬ 346 < 6), entry_346_checked]
  change forkRow [placeRow ⟨60, 1, 4, 3⟩ (rowAt 60), placeRow ⟨255, 0, 1, 4⟩ (rowAt 255), placeRow ⟨276, 0, 1, 4⟩ (rowAt 276)] = data_346
  rw [row_60, row_255, row_276]
  apply row_ext <;> decide +kernel
theorem entry_good_346 : EntryGood 346 := by
  unfold EntryGood
  rw [entry_346_checked]
  decide +kernel
theorem good_346 : Good (rowAt 346) := by
  rw [row_346]
  unfold Good
  decide +kernel

theorem entry_347_checked : entryAt 347 = entry_347 := by
  rw [entry_chunk_17 1 (by decide)]
  decide +kernel
theorem row_347 : rowAt 347 = data_347 := by
  rw [rowAt, dif_neg (by decide : ¬ 347 < 6), entry_347_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨339, 0, 5, 8⟩ (rowAt 339)] = data_347
  rw [row_6, row_339]
  apply row_ext <;> decide +kernel
theorem entry_good_347 : EntryGood 347 := by
  unfold EntryGood
  rw [entry_347_checked]
  decide +kernel
theorem good_347 : Good (rowAt 347) := by
  rw [row_347]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 344 = data_344 ∧ Good (rowAt 344) ∧ EntryGood 344) ∧ (rowAt 345 = data_345 ∧ Good (rowAt 345) ∧ EntryGood 345) ∧ (rowAt 346 = data_346 ∧ Good (rowAt 346) ∧ EntryGood 346) ∧ (rowAt 347 = data_347 ∧ Good (rowAt 347) ∧ EntryGood 347) ∧ True := by
  exact ⟨⟨row_344, good_344, entry_good_344⟩, ⟨row_345, good_345, entry_good_345⟩, ⟨row_346, good_346, entry_good_346⟩, ⟨row_347, good_347, entry_good_347⟩, trivial⟩
