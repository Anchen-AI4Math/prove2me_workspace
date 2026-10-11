import Definitions.Def_Snaky35Cache11
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_17 (j : ℕ) (hj : j < 20) : entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_82 : rowAt 82 = data_82 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_91 : rowAt 91 = data_91 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_114 : rowAt 114 = data_114 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_134 : rowAt 134 = data_134 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.1).1
theorem row_138 : rowAt 138 = data_138 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_179 : rowAt 179 = data_179 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_182 : rowAt 182 = data_182 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_211 : rowAt 211 = data_211 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_214 : rowAt 214 = data_214 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_283 : rowAt 283 = data_283 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_312 : rowAt 312 = data_312 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_323 : rowAt 323 = data_323 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.1).1
theorem row_342 : rowAt 342 = data_342 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_344 : rowAt 344 = data_344 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_346 : rowAt 346 = data_346 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_347 : rowAt 347 = data_347 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_356_checked : entryAt 356 = entry_356 := by
  rw [entry_chunk_17 10 (by decide)]
  decide +kernel
theorem row_356 : rowAt 356 = data_356 := by
  rw [rowAt, dif_neg (by decide : ¬ 356 < 6), entry_356_checked]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨179, 0, 6, 4⟩ (rowAt 179)] = data_356
  rw [row_24, row_211, row_179]
  apply row_ext <;> decide +kernel
theorem entry_good_356 : EntryGood 356 := by
  unfold EntryGood
  rw [entry_356_checked]
  decide +kernel
theorem good_356 : Good (rowAt 356) := by
  rw [row_356]
  unfold Good
  decide +kernel

theorem entry_357_checked : entryAt 357 = entry_357 := by
  rw [entry_chunk_17 11 (by decide)]
  decide +kernel
theorem row_357 : rowAt 357 = data_357 := by
  rw [rowAt, dif_neg (by decide : ¬ 357 < 6), entry_357_checked]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (rowAt 82), placeRow ⟨283, 0, 5, 6⟩ (rowAt 283)] = data_357
  rw [row_82, row_283]
  apply row_ext <;> decide +kernel
theorem entry_good_357 : EntryGood 357 := by
  unfold EntryGood
  rw [entry_357_checked]
  decide +kernel
theorem good_357 : Good (rowAt 357) := by
  rw [row_357]
  unfold Good
  decide +kernel

theorem entry_358_checked : entryAt 358 = entry_358 := by
  rw [entry_chunk_17 12 (by decide)]
  decide +kernel
theorem row_358 : rowAt 358 = data_358 := by
  rw [rowAt, dif_neg (by decide : ¬ 358 < 6), entry_358_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨346, 0, 4, 6⟩ (rowAt 346)] = data_358
  rw [row_6, row_346]
  apply row_ext <;> decide +kernel
theorem entry_good_358 : EntryGood 358 := by
  unfold EntryGood
  rw [entry_358_checked]
  decide +kernel
theorem good_358 : Good (rowAt 358) := by
  rw [row_358]
  unfold Good
  decide +kernel

theorem entry_359_checked : entryAt 359 = entry_359 := by
  rw [entry_chunk_17 13 (by decide)]
  decide +kernel
theorem row_359 : rowAt 359 = data_359 := by
  rw [rowAt, dif_neg (by decide : ¬ 359 < 6), entry_359_checked]
  change forkRow [placeRow ⟨134, 0, 4, 6⟩ (rowAt 134), placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨323, 0, 5, 5⟩ (rowAt 323)] = data_359
  rw [row_134, row_24, row_323]
  apply row_ext <;> decide +kernel
theorem entry_good_359 : EntryGood 359 := by
  unfold EntryGood
  rw [entry_359_checked]
  decide +kernel
theorem good_359 : Good (rowAt 359) := by
  rw [row_359]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 356 = data_356 ∧ Good (rowAt 356) ∧ EntryGood 356) ∧ (rowAt 357 = data_357 ∧ Good (rowAt 357) ∧ EntryGood 357) ∧ (rowAt 358 = data_358 ∧ Good (rowAt 358) ∧ EntryGood 358) ∧ (rowAt 359 = data_359 ∧ Good (rowAt 359) ∧ EntryGood 359) ∧ True := by
  exact ⟨⟨row_356, good_356, entry_good_356⟩, ⟨row_357, good_357, entry_good_357⟩, ⟨row_358, good_358, entry_good_358⟩, ⟨row_359, good_359, entry_good_359⟩, trivial⟩
