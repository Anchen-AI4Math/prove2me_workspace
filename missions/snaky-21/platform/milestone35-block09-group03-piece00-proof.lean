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
theorem entry_312_checked : entryAt 312 = entry_312 := by
  rw [entry_chunk_15 6 (by decide)]
  decide +kernel
theorem row_312 : rowAt 312 = data_312 := by
  rw [rowAt, dif_neg (by decide : ¬ 312 < 6), entry_312_checked]
  change forkRow [placeRow ⟨9, 2, 5, 4⟩ (rowAt 9), placeRow ⟨272, 0, 4, 5⟩ (rowAt 272)] = data_312
  rw [row_9, row_272]
  apply row_ext <;> decide +kernel
theorem entry_good_312 : EntryGood 312 := by
  unfold EntryGood
  rw [entry_312_checked]
  decide +kernel
theorem good_312 : Good (rowAt 312) := by
  rw [row_312]
  unfold Good
  decide +kernel

theorem entry_313_checked : entryAt 313 = entry_313 := by
  rw [entry_chunk_15 7 (by decide)]
  decide +kernel
theorem row_313 : rowAt 313 = data_313 := by
  rw [rowAt, dif_neg (by decide : ¬ 313 < 6), entry_313_checked]
  change forkRow [placeRow ⟨162, 4, 4, 5⟩ (rowAt 162), placeRow ⟨148, 5, 6, 3⟩ (rowAt 148)] = data_313
  rw [row_162, row_148]
  apply row_ext <;> decide +kernel
theorem entry_good_313 : EntryGood 313 := by
  unfold EntryGood
  rw [entry_313_checked]
  decide +kernel
theorem good_313 : Good (rowAt 313) := by
  rw [row_313]
  unfold Good
  decide +kernel

theorem entry_314_checked : entryAt 314 = entry_314 := by
  rw [entry_chunk_15 8 (by decide)]
  decide +kernel
theorem row_314 : rowAt 314 = data_314 := by
  rw [rowAt, dif_neg (by decide : ¬ 314 < 6), entry_314_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨305, 0, 6, 4⟩ (rowAt 305)] = data_314
  rw [row_6, row_305]
  apply row_ext <;> decide +kernel
theorem entry_good_314 : EntryGood 314 := by
  unfold EntryGood
  rw [entry_314_checked]
  decide +kernel
theorem good_314 : Good (rowAt 314) := by
  rw [row_314]
  unfold Good
  decide +kernel

theorem entry_315_checked : entryAt 315 = entry_315 := by
  rw [entry_chunk_15 9 (by decide)]
  decide +kernel
theorem row_315 : rowAt 315 = data_315 := by
  rw [rowAt, dif_neg (by decide : ¬ 315 < 6), entry_315_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨296, 0, 4, 5⟩ (rowAt 296)] = data_315
  rw [row_6, row_296]
  apply row_ext <;> decide +kernel
theorem entry_good_315 : EntryGood 315 := by
  unfold EntryGood
  rw [entry_315_checked]
  decide +kernel
theorem good_315 : Good (rowAt 315) := by
  rw [row_315]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 312 = data_312 ∧ Good (rowAt 312) ∧ EntryGood 312) ∧ (rowAt 313 = data_313 ∧ Good (rowAt 313) ∧ EntryGood 313) ∧ (rowAt 314 = data_314 ∧ Good (rowAt 314) ∧ EntryGood 314) ∧ (rowAt 315 = data_315 ∧ Good (rowAt 315) ∧ EntryGood 315) ∧ True := by
  exact ⟨⟨row_312, good_312, entry_good_312⟩, ⟨row_313, good_313, entry_good_313⟩, ⟨row_314, good_314, entry_good_314⟩, ⟨row_315, good_315, entry_good_315⟩, trivial⟩
