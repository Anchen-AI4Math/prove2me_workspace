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
theorem entry_352_checked : entryAt 352 = entry_352 := by
  rw [entry_chunk_17 6 (by decide)]
  decide +kernel
theorem row_352 : rowAt 352 = data_352 := by
  rw [rowAt, dif_neg (by decide : ¬ 352 < 6), entry_352_checked]
  change forkRow [placeRow ⟨214, 0, 4, 5⟩ (rowAt 214), placeRow ⟨91, 0, 3, 4⟩ (rowAt 91), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨344, 0, 4, 5⟩ (rowAt 344), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180)] = data_352
  rw [row_214, row_91, row_63, row_344, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_352 : EntryGood 352 := by
  unfold EntryGood
  rw [entry_352_checked]
  decide +kernel
theorem good_352 : Good (rowAt 352) := by
  rw [row_352]
  unfold Good
  decide +kernel

theorem entry_353_checked : entryAt 353 = entry_353 := by
  rw [entry_chunk_17 7 (by decide)]
  decide +kernel
theorem row_353 : rowAt 353 = data_353 := by
  rw [rowAt, dif_neg (by decide : ¬ 353 < 6), entry_353_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨347, 0, 1, 3⟩ (rowAt 347)] = data_353
  rw [row_6, row_347]
  apply row_ext <;> decide +kernel
theorem entry_good_353 : EntryGood 353 := by
  unfold EntryGood
  rw [entry_353_checked]
  decide +kernel
theorem good_353 : Good (rowAt 353) := by
  rw [row_353]
  unfold Good
  decide +kernel

theorem entry_354_checked : entryAt 354 = entry_354 := by
  rw [entry_chunk_17 8 (by decide)]
  decide +kernel
theorem row_354 : rowAt 354 = data_354 := by
  rw [rowAt, dif_neg (by decide : ¬ 354 < 6), entry_354_checked]
  change forkRow [placeRow ⟨138, 2, 5, 4⟩ (rowAt 138), placeRow ⟨114, 5, 4, 3⟩ (rowAt 114), placeRow ⟨312, 0, 5, 5⟩ (rowAt 312), placeRow ⟨182, 2, 2, 4⟩ (rowAt 182)] = data_354
  rw [row_138, row_114, row_312, row_182]
  apply row_ext <;> decide +kernel
theorem entry_good_354 : EntryGood 354 := by
  unfold EntryGood
  rw [entry_354_checked]
  decide +kernel
theorem good_354 : Good (rowAt 354) := by
  rw [row_354]
  unfold Good
  decide +kernel

theorem entry_355_checked : entryAt 355 = entry_355 := by
  rw [entry_chunk_17 9 (by decide)]
  decide +kernel
theorem row_355 : rowAt 355 = data_355 := by
  rw [rowAt, dif_neg (by decide : ¬ 355 < 6), entry_355_checked]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (rowAt 12), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨342, 0, 6, 6⟩ (rowAt 342)] = data_355
  rw [row_12, row_167, row_342]
  apply row_ext <;> decide +kernel
theorem entry_good_355 : EntryGood 355 := by
  unfold EntryGood
  rw [entry_355_checked]
  decide +kernel
theorem good_355 : Good (rowAt 355) := by
  rw [row_355]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 352 = data_352 ∧ Good (rowAt 352) ∧ EntryGood 352) ∧ (rowAt 353 = data_353 ∧ Good (rowAt 353) ∧ EntryGood 353) ∧ (rowAt 354 = data_354 ∧ Good (rowAt 354) ∧ EntryGood 354) ∧ (rowAt 355 = data_355 ∧ Good (rowAt 355) ∧ EntryGood 355) ∧ True := by
  exact ⟨⟨row_352, good_352, entry_good_352⟩, ⟨row_353, good_353, entry_good_353⟩, ⟨row_354, good_354, entry_good_354⟩, ⟨row_355, good_355, entry_good_355⟩, trivial⟩
