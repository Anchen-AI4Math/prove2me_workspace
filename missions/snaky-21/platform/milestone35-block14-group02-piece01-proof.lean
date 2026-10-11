import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group02_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_22 (j : ℕ) (hj : j < 20) : entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_23 (j : ℕ) (hj : j < 20) : entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_224 : rowAt 224 = data_224 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.1).1
theorem row_285 : rowAt 285 = data_285 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_306 : rowAt 306 = data_306 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_315 : rowAt 315 = data_315 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_324 : rowAt 324 = data_324 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.1).1
theorem row_325 : rowAt 325 = data_325 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.1).1
theorem row_358 : rowAt 358 = data_358 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.1).1
theorem row_360 : rowAt 360 = data_360 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.1).1
theorem row_395 : rowAt 395 = data_395 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_417 : rowAt 417 = data_417 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_461 : rowAt 461 = data_461 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_correct.2.2.2.2.2.1).1
theorem row_464 : rowAt 464 = data_464 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.1).1
theorem row_466 : rowAt 466 = data_466 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.2.2.1).1
theorem entry_468_checked : entryAt 468 = entry_468 := by
  rw [entry_chunk_23 2 (by decide)]
  decide +kernel
theorem row_468 : rowAt 468 = data_468 := by
  rw [rowAt, dif_neg (by decide : ¬ 468 < 6), entry_468_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨464, 0, 4, 7⟩ (rowAt 464)] = data_468
  rw [row_6, row_464]
  apply row_ext <;> decide +kernel
theorem entry_good_468 : EntryGood 468 := by
  unfold EntryGood
  rw [entry_468_checked]
  decide +kernel
theorem good_468 : Good (rowAt 468) := by
  rw [row_468]
  unfold Good
  decide +kernel

theorem entry_469_checked : entryAt 469 = entry_469 := by
  rw [entry_chunk_23 3 (by decide)]
  decide +kernel
theorem row_469 : rowAt 469 = data_469 := by
  rw [rowAt, dif_neg (by decide : ¬ 469 < 6), entry_469_checked]
  change forkRow [placeRow ⟨55, 5, 4, 3⟩ (rowAt 55), placeRow ⟨443, 1, 5, 7⟩ (rowAt 443), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314)] = data_469
  rw [row_55, row_443, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_469 : EntryGood 469 := by
  unfold EntryGood
  rw [entry_469_checked]
  decide +kernel
theorem good_469 : Good (rowAt 469) := by
  rw [row_469]
  unfold Good
  decide +kernel

theorem entry_470_checked : entryAt 470 = entry_470 := by
  rw [entry_chunk_23 4 (by decide)]
  decide +kernel
theorem row_470 : rowAt 470 = data_470 := by
  rw [rowAt, dif_neg (by decide : ¬ 470 < 6), entry_470_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨468, 0, 4, 2⟩ (rowAt 468)] = data_470
  rw [row_6, row_468]
  apply row_ext <;> decide +kernel
theorem entry_good_470 : EntryGood 470 := by
  unfold EntryGood
  rw [entry_470_checked]
  decide +kernel
theorem good_470 : Good (rowAt 470) := by
  rw [row_470]
  unfold Good
  decide +kernel

theorem entry_471_checked : entryAt 471 = entry_471 := by
  rw [entry_chunk_23 5 (by decide)]
  decide +kernel
theorem row_471 : rowAt 471 = data_471 := by
  rw [rowAt, dif_neg (by decide : ¬ 471 < 6), entry_471_checked]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (rowAt 6), placeRow ⟨466, 0, 5, 6⟩ (rowAt 466)] = data_471
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_471 : EntryGood 471 := by
  unfold EntryGood
  rw [entry_471_checked]
  decide +kernel
theorem good_471 : Good (rowAt 471) := by
  rw [row_471]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 468 = data_468 ∧ Good (rowAt 468) ∧ EntryGood 468) ∧ (rowAt 469 = data_469 ∧ Good (rowAt 469) ∧ EntryGood 469) ∧ (rowAt 470 = data_470 ∧ Good (rowAt 470) ∧ EntryGood 470) ∧ (rowAt 471 = data_471 ∧ Good (rowAt 471) ∧ EntryGood 471) ∧ True := by
  exact ⟨⟨row_468, good_468, entry_good_468⟩, ⟨row_469, good_469, entry_good_469⟩, ⟨row_470, good_470, entry_good_470⟩, ⟨row_471, good_471, entry_good_471⟩, trivial⟩
