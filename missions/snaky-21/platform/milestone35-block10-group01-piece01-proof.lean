import Definitions.Def_Snaky35Cache10
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
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_15 : rowAt 15 = data_15 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.1).1
theorem row_90 : rowAt 90 = data_90 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_113 : rowAt 113 = data_113 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_154 : rowAt 154 = data_154 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_155 : rowAt 155 = data_155 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_196 : rowAt 196 = data_196 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.1).1
theorem row_268 : rowAt 268 = data_268 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_285 : rowAt 285 = data_285 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_289 : rowAt 289 = data_289 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_305 : rowAt 305 = data_305 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_317 : rowAt 317 = data_317 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_332_checked : entryAt 332 = entry_332 := by
  rw [entry_chunk_16 6 (by decide)]
  decide +kernel
theorem row_332 : rowAt 332 = data_332 := by
  rw [rowAt, dif_neg (by decide : ¬ 332 < 6), entry_332_checked]
  change forkRow [placeRow ⟨67, 4, 3, 4⟩ (rowAt 67), placeRow ⟨289, 2, 5, 1⟩ (rowAt 289)] = data_332
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_332 : EntryGood 332 := by
  unfold EntryGood
  rw [entry_332_checked]
  decide +kernel
theorem good_332 : Good (rowAt 332) := by
  rw [row_332]
  unfold Good
  decide +kernel

theorem entry_333_checked : entryAt 333 = entry_333 := by
  rw [entry_chunk_16 7 (by decide)]
  decide +kernel
theorem row_333 : rowAt 333 = data_333 := by
  rw [rowAt, dif_neg (by decide : ¬ 333 < 6), entry_333_checked]
  change forkRow [placeRow ⟨317, 0, 5, 4⟩ (rowAt 317), placeRow ⟨1, 5, 4, 3⟩ (rowAt 1)] = data_333
  rw [row_317, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_333 : EntryGood 333 := by
  unfold EntryGood
  rw [entry_333_checked]
  decide +kernel
theorem good_333 : Good (rowAt 333) := by
  rw [row_333]
  unfold Good
  decide +kernel

theorem entry_334_checked : entryAt 334 = entry_334 := by
  rw [entry_chunk_16 8 (by decide)]
  decide +kernel
theorem row_334 : rowAt 334 = data_334 := by
  rw [rowAt, dif_neg (by decide : ¬ 334 < 6), entry_334_checked]
  change forkRow [placeRow ⟨67, 6, 3, 2⟩ (rowAt 67), placeRow ⟨289, 0, 5, 5⟩ (rowAt 289)] = data_334
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_334 : EntryGood 334 := by
  unfold EntryGood
  rw [entry_334_checked]
  decide +kernel
theorem good_334 : Good (rowAt 334) := by
  rw [row_334]
  unfold Good
  decide +kernel

theorem entry_335_checked : entryAt 335 = entry_335 := by
  rw [entry_chunk_16 9 (by decide)]
  decide +kernel
theorem row_335 : rowAt 335 = data_335 := by
  rw [rowAt, dif_neg (by decide : ¬ 335 < 6), entry_335_checked]
  change forkRow [placeRow ⟨196, 3, 1, 3⟩ (rowAt 196), placeRow ⟨162, 1, 5, 4⟩ (rowAt 162)] = data_335
  rw [row_196, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_335 : EntryGood 335 := by
  unfold EntryGood
  rw [entry_335_checked]
  decide +kernel
theorem good_335 : Good (rowAt 335) := by
  rw [row_335]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 332 = data_332 ∧ Good (rowAt 332) ∧ EntryGood 332) ∧ (rowAt 333 = data_333 ∧ Good (rowAt 333) ∧ EntryGood 333) ∧ (rowAt 334 = data_334 ∧ Good (rowAt 334) ∧ EntryGood 334) ∧ (rowAt 335 = data_335 ∧ Good (rowAt 335) ∧ EntryGood 335) ∧ True := by
  exact ⟨⟨row_332, good_332, entry_good_332⟩, ⟨row_333, good_333, entry_good_333⟩, ⟨row_334, good_334, entry_good_334⟩, ⟨row_335, good_335, entry_good_335⟩, trivial⟩
