import Definitions.Def_Snaky35Cache11
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_18 (j : ℕ) (hj : j < 20) : entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_40 : rowAt 40 = data_40 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.1).1
theorem row_80 : rowAt 80 = data_80 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_120 : rowAt 120 = data_120 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_137 : rowAt 137 = data_137 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_156 : rowAt 156 = data_156 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_161 : rowAt 161 = data_161 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_199 : rowAt 199 = data_199 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_267 : rowAt 267 = data_267 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_286 : rowAt 286 = data_286 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_327 : rowAt 327 = data_327 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.1).1
theorem row_333 : rowAt 333 = data_333 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_335 : rowAt 335 = data_335 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_366 : rowAt 366 = data_366 := (OAI.SnakyCertificate.MilestoneChecks.block11_group01_correct.2.2.2.2.2.2.1).1
theorem row_367 : rowAt 367 = data_367 := (OAI.SnakyCertificate.MilestoneChecks.block11_group01_correct.2.2.2.2.2.2.2.1).1
theorem entry_368_checked : entryAt 368 = entry_368 := by
  rw [entry_chunk_18 2 (by decide)]
  decide +kernel
theorem row_368 : rowAt 368 = data_368 := by
  rw [rowAt, dif_neg (by decide : ¬ 368 < 6), entry_368_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨366, 0, 2, 4⟩ (rowAt 366)] = data_368
  rw [row_6, row_366]
  apply row_ext <;> decide +kernel
theorem entry_good_368 : EntryGood 368 := by
  unfold EntryGood
  rw [entry_368_checked]
  decide +kernel
theorem good_368 : Good (rowAt 368) := by
  rw [row_368]
  unfold Good
  decide +kernel

theorem entry_369_checked : entryAt 369 = entry_369 := by
  rw [entry_chunk_18 3 (by decide)]
  decide +kernel
theorem row_369 : rowAt 369 = data_369 := by
  rw [rowAt, dif_neg (by decide : ¬ 369 < 6), entry_369_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨367, 4, 1, 2⟩ (rowAt 367)] = data_369
  rw [row_6, row_367]
  apply row_ext <;> decide +kernel
theorem entry_good_369 : EntryGood 369 := by
  unfold EntryGood
  rw [entry_369_checked]
  decide +kernel
theorem good_369 : Good (rowAt 369) := by
  rw [row_369]
  unfold Good
  decide +kernel

theorem entry_370_checked : entryAt 370 = entry_370 := by
  rw [entry_chunk_18 4 (by decide)]
  decide +kernel
theorem row_370 : rowAt 370 = data_370 := by
  rw [rowAt, dif_neg (by decide : ¬ 370 < 6), entry_370_checked]
  change forkRow [placeRow ⟨199, 3, 1, 4⟩ (rowAt 199), placeRow ⟨286, 1, 5, 4⟩ (rowAt 286), placeRow ⟨24, 6, 1, 3⟩ (rowAt 24), placeRow ⟨319, 0, 5, 3⟩ (rowAt 319)] = data_370
  rw [row_199, row_286, row_24, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_370 : EntryGood 370 := by
  unfold EntryGood
  rw [entry_370_checked]
  decide +kernel
theorem good_370 : Good (rowAt 370) := by
  rw [row_370]
  unfold Good
  decide +kernel

theorem entry_371_checked : entryAt 371 = entry_371 := by
  rw [entry_chunk_18 5 (by decide)]
  decide +kernel
theorem row_371 : rowAt 371 = data_371 := by
  rw [rowAt, dif_neg (by decide : ¬ 371 < 6), entry_371_checked]
  change forkRow [placeRow ⟨267, 6, 2, 4⟩ (rowAt 267), placeRow ⟨137, 1, 4, 2⟩ (rowAt 137)] = data_371
  rw [row_267, row_137]
  apply row_ext <;> decide +kernel
theorem entry_good_371 : EntryGood 371 := by
  unfold EntryGood
  rw [entry_371_checked]
  decide +kernel
theorem good_371 : Good (rowAt 371) := by
  rw [row_371]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 368 = data_368 ∧ Good (rowAt 368) ∧ EntryGood 368) ∧ (rowAt 369 = data_369 ∧ Good (rowAt 369) ∧ EntryGood 369) ∧ (rowAt 370 = data_370 ∧ Good (rowAt 370) ∧ EntryGood 370) ∧ (rowAt 371 = data_371 ∧ Good (rowAt 371) ∧ EntryGood 371) ∧ True := by
  exact ⟨⟨row_368, good_368, entry_good_368⟩, ⟨row_369, good_369, entry_good_369⟩, ⟨row_370, good_370, entry_good_370⟩, ⟨row_371, good_371, entry_good_371⟩, trivial⟩
