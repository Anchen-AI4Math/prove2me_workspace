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
theorem entry_372_checked : entryAt 372 = entry_372 := by
  rw [entry_chunk_18 6 (by decide)]
  decide +kernel
theorem row_372 : rowAt 372 = data_372 := by
  rw [rowAt, dif_neg (by decide : ¬ 372 < 6), entry_372_checked]
  change forkRow [placeRow ⟨40, 1, 4, 3⟩ (rowAt 40), placeRow ⟨333, 0, 2, 4⟩ (rowAt 333), placeRow ⟨120, 1, 3, 3⟩ (rowAt 120), placeRow ⟨161, 0, 4, 2⟩ (rowAt 161)] = data_372
  rw [row_40, row_333, row_120, row_161]
  apply row_ext <;> decide +kernel
theorem entry_good_372 : EntryGood 372 := by
  unfold EntryGood
  rw [entry_372_checked]
  decide +kernel
theorem good_372 : Good (rowAt 372) := by
  rw [row_372]
  unfold Good
  decide +kernel

theorem entry_373_checked : entryAt 373 = entry_373 := by
  rw [entry_chunk_18 7 (by decide)]
  decide +kernel
theorem row_373 : rowAt 373 = data_373 := by
  rw [rowAt, dif_neg (by decide : ¬ 373 < 6), entry_373_checked]
  change forkRow [placeRow ⟨156, 2, 7, 4⟩ (rowAt 156), placeRow ⟨226, 4, 3, 5⟩ (rowAt 226), placeRow ⟨80, 0, 5, 4⟩ (rowAt 80), placeRow ⟨327, 0, 5, 5⟩ (rowAt 327), placeRow ⟨156, 6, 3, 4⟩ (rowAt 156)] = data_373
  rw [row_156, row_226, row_80, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_373 : EntryGood 373 := by
  unfold EntryGood
  rw [entry_373_checked]
  decide +kernel
theorem good_373 : Good (rowAt 373) := by
  rw [row_373]
  unfold Good
  decide +kernel

theorem entry_374_checked : entryAt 374 = entry_374 := by
  rw [entry_chunk_18 8 (by decide)]
  decide +kernel
theorem row_374 : rowAt 374 = data_374 := by
  rw [rowAt, dif_neg (by decide : ¬ 374 < 6), entry_374_checked]
  change forkRow [placeRow ⟨65, 4, 3, 4⟩ (rowAt 65), placeRow ⟨335, 0, 7, 4⟩ (rowAt 335), placeRow ⟨24, 2, 7, 3⟩ (rowAt 24), placeRow ⟨163, 4, 3, 4⟩ (rowAt 163)] = data_374
  rw [row_65, row_335, row_24, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_374 : EntryGood 374 := by
  unfold EntryGood
  rw [entry_374_checked]
  decide +kernel
theorem good_374 : Good (rowAt 374) := by
  rw [row_374]
  unfold Good
  decide +kernel

theorem entry_375_checked : entryAt 375 = entry_375 := by
  rw [entry_chunk_18 9 (by decide)]
  decide +kernel
theorem row_375 : rowAt 375 = data_375 := by
  rw [rowAt, dif_neg (by decide : ¬ 375 < 6), entry_375_checked]
  change forkRow [placeRow ⟨24, 3, 3, 6⟩ (rowAt 24), placeRow ⟨327, 6, 3, 3⟩ (rowAt 327)] = data_375
  rw [row_24, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_375 : EntryGood 375 := by
  unfold EntryGood
  rw [entry_375_checked]
  decide +kernel
theorem good_375 : Good (rowAt 375) := by
  rw [row_375]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 372 = data_372 ∧ Good (rowAt 372) ∧ EntryGood 372) ∧ (rowAt 373 = data_373 ∧ Good (rowAt 373) ∧ EntryGood 373) ∧ (rowAt 374 = data_374 ∧ Good (rowAt 374) ∧ EntryGood 374) ∧ (rowAt 375 = data_375 ∧ Good (rowAt 375) ∧ EntryGood 375) ∧ True := by
  exact ⟨⟨row_372, good_372, entry_good_372⟩, ⟨row_373, good_373, entry_good_373⟩, ⟨row_374, good_374, entry_good_374⟩, ⟨row_375, good_375, entry_good_375⟩, trivial⟩
