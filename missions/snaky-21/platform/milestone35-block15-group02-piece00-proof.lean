import Definitions.Def_Snaky35Cache15
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_24 (j : ℕ) (hj : j < 20) : entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_232 : rowAt 232 = data_232 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_316 : rowAt 316 = data_316 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_351 : rowAt 351 = data_351 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_410 : rowAt 410 = data_410 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_419 : rowAt 419 = data_419 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.1).1
theorem row_420 : rowAt 420 = data_420 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.1).1
theorem row_478 : rowAt 478 = data_478 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_493 : rowAt 493 = data_493 := (OAI.SnakyCertificate.MilestoneChecks.block15_group01_correct.2.2.2.2.2.1).1
theorem row_494 : rowAt 494 = data_494 := (OAI.SnakyCertificate.MilestoneChecks.block15_group01_correct.2.2.2.2.2.2.1).1
theorem entry_496_checked : entryAt 496 = entry_496 := by
  rw [entry_chunk_24 10 (by decide)]
  decide +kernel
theorem row_496 : rowAt 496 = data_496 := by
  rw [rowAt, dif_neg (by decide : ¬ 496 < 6), entry_496_checked]
  change forkRow [placeRow ⟨25, 0, 7, 5⟩ (rowAt 25), placeRow ⟨107, 6, 3, 4⟩ (rowAt 107), placeRow ⟨163, 6, 3, 4⟩ (rowAt 163), placeRow ⟨494, 0, 7, 4⟩ (rowAt 494)] = data_496
  rw [row_25, row_107, row_163, row_494]
  apply row_ext <;> decide +kernel
theorem entry_good_496 : EntryGood 496 := by
  unfold EntryGood
  rw [entry_496_checked]
  decide +kernel
theorem good_496 : Good (rowAt 496) := by
  rw [row_496]
  unfold Good
  decide +kernel

theorem entry_497_checked : entryAt 497 = entry_497 := by
  rw [entry_chunk_24 11 (by decide)]
  decide +kernel
theorem row_497 : rowAt 497 = data_497 := by
  rw [rowAt, dif_neg (by decide : ¬ 497 < 6), entry_497_checked]
  change forkRow [placeRow ⟨36, 2, 3, 4⟩ (rowAt 36), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨410, 0, 7, 3⟩ (rowAt 410)] = data_497
  rw [row_36, row_167, row_410]
  apply row_ext <;> decide +kernel
theorem entry_good_497 : EntryGood 497 := by
  unfold EntryGood
  rw [entry_497_checked]
  decide +kernel
theorem good_497 : Good (rowAt 497) := by
  rw [row_497]
  unfold Good
  decide +kernel

theorem entry_498_checked : entryAt 498 = entry_498 := by
  rw [entry_chunk_24 12 (by decide)]
  decide +kernel
theorem row_498 : rowAt 498 = data_498 := by
  rw [rowAt, dif_neg (by decide : ¬ 498 < 6), entry_498_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨298, 2, 2, 4⟩ (rowAt 298)] = data_498
  rw [row_14, row_298]
  apply row_ext <;> decide +kernel
theorem entry_good_498 : EntryGood 498 := by
  unfold EntryGood
  rw [entry_498_checked]
  decide +kernel
theorem good_498 : Good (rowAt 498) := by
  rw [row_498]
  unfold Good
  decide +kernel

theorem entry_499_checked : entryAt 499 = entry_499 := by
  rw [entry_chunk_24 13 (by decide)]
  decide +kernel
theorem row_499 : rowAt 499 = data_499 := by
  rw [rowAt, dif_neg (by decide : ¬ 499 < 6), entry_499_checked]
  change forkRow [placeRow ⟨493, 0, 5, 4⟩ (rowAt 493), placeRow ⟨25, 1, 4, 5⟩ (rowAt 25), placeRow ⟨478, 0, 2, 4⟩ (rowAt 478)] = data_499
  rw [row_493, row_25, row_478]
  apply row_ext <;> decide +kernel
theorem entry_good_499 : EntryGood 499 := by
  unfold EntryGood
  rw [entry_499_checked]
  decide +kernel
theorem good_499 : Good (rowAt 499) := by
  rw [row_499]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 496 = data_496 ∧ Good (rowAt 496) ∧ EntryGood 496) ∧ (rowAt 497 = data_497 ∧ Good (rowAt 497) ∧ EntryGood 497) ∧ (rowAt 498 = data_498 ∧ Good (rowAt 498) ∧ EntryGood 498) ∧ (rowAt 499 = data_499 ∧ Good (rowAt 499) ∧ EntryGood 499) ∧ True := by
  exact ⟨⟨row_496, good_496, entry_good_496⟩, ⟨row_497, good_497, entry_good_497⟩, ⟨row_498, good_498, entry_good_498⟩, ⟨row_499, good_499, entry_good_499⟩, trivial⟩
