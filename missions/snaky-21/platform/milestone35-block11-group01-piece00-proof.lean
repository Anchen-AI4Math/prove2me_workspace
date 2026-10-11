import Definitions.Def_Snaky35Cache11
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_17 (j : ℕ) (hj : j < 20) : entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_18 (j : ℕ) (hj : j < 20) : entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_137 : rowAt 137 = data_137 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_155 : rowAt 155 = data_155 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_228 : rowAt 228 = data_228 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.1).1
theorem row_248 : rowAt 248 = data_248 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_337 : rowAt 337 = data_337 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_345 : rowAt 345 = data_345 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_352 : rowAt 352 = data_352 := (OAI.SnakyCertificate.MilestoneChecks.block11_group00_correct.1).1
theorem row_354 : rowAt 354 = data_354 := (OAI.SnakyCertificate.MilestoneChecks.block11_group00_correct.2.2.1).1
theorem row_357 : rowAt 357 = data_357 := (OAI.SnakyCertificate.MilestoneChecks.block11_group00_correct.2.2.2.2.2.1).1
theorem entry_360_checked : entryAt 360 = entry_360 := by
  rw [entry_chunk_17 14 (by decide)]
  decide +kernel
theorem row_360 : rowAt 360 = data_360 := by
  rw [rowAt, dif_neg (by decide : ¬ 360 < 6), entry_360_checked]
  change forkRow [placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨337, 0, 5, 2⟩ (rowAt 337), placeRow ⟨228, 4, 5, 2⟩ (rowAt 228)] = data_360
  rw [row_155, row_7, row_337, row_228]
  apply row_ext <;> decide +kernel
theorem entry_good_360 : EntryGood 360 := by
  unfold EntryGood
  rw [entry_360_checked]
  decide +kernel
theorem good_360 : Good (rowAt 360) := by
  rw [row_360]
  unfold Good
  decide +kernel

theorem entry_361_checked : entryAt 361 = entry_361 := by
  rw [entry_chunk_17 15 (by decide)]
  decide +kernel
theorem row_361 : rowAt 361 = data_361 := by
  rw [rowAt, dif_neg (by decide : ¬ 361 < 6), entry_361_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨352, 0, 4, 5⟩ (rowAt 352)] = data_361
  rw [row_6, row_352]
  apply row_ext <;> decide +kernel
theorem entry_good_361 : EntryGood 361 := by
  unfold EntryGood
  rw [entry_361_checked]
  decide +kernel
theorem good_361 : Good (rowAt 361) := by
  rw [row_361]
  unfold Good
  decide +kernel

theorem entry_362_checked : entryAt 362 = entry_362 := by
  rw [entry_chunk_17 16 (by decide)]
  decide +kernel
theorem row_362 : rowAt 362 = data_362 := by
  rw [rowAt, dif_neg (by decide : ¬ 362 < 6), entry_362_checked]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (rowAt 4), placeRow ⟨345, 0, 4, 3⟩ (rowAt 345)] = data_362
  rw [row_4, row_345]
  apply row_ext <;> decide +kernel
theorem entry_good_362 : EntryGood 362 := by
  unfold EntryGood
  rw [entry_362_checked]
  decide +kernel
theorem good_362 : Good (rowAt 362) := by
  rw [row_362]
  unfold Good
  decide +kernel

theorem entry_363_checked : entryAt 363 = entry_363 := by
  rw [entry_chunk_17 17 (by decide)]
  decide +kernel
theorem row_363 : rowAt 363 = data_363 := by
  rw [rowAt, dif_neg (by decide : ¬ 363 < 6), entry_363_checked]
  change forkRow [placeRow ⟨137, 1, 4, 2⟩ (rowAt 137), placeRow ⟨248, 0, 2, 4⟩ (rowAt 248)] = data_363
  rw [row_137, row_248]
  apply row_ext <;> decide +kernel
theorem entry_good_363 : EntryGood 363 := by
  unfold EntryGood
  rw [entry_363_checked]
  decide +kernel
theorem good_363 : Good (rowAt 363) := by
  rw [row_363]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 360 = data_360 ∧ Good (rowAt 360) ∧ EntryGood 360) ∧ (rowAt 361 = data_361 ∧ Good (rowAt 361) ∧ EntryGood 361) ∧ (rowAt 362 = data_362 ∧ Good (rowAt 362) ∧ EntryGood 362) ∧ (rowAt 363 = data_363 ∧ Good (rowAt 363) ∧ EntryGood 363) ∧ True := by
  exact ⟨⟨row_360, good_360, entry_good_360⟩, ⟨row_361, good_361, entry_good_361⟩, ⟨row_362, good_362, entry_good_362⟩, ⟨row_363, good_363, entry_good_363⟩, trivial⟩
