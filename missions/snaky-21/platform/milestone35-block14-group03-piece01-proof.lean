import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group03_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_23 (j : ℕ) (hj : j < 20) : entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_70 : rowAt 70 = data_70 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.1).1
theorem row_83 : rowAt 83 = data_83 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_121 : rowAt 121 = data_121 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_154 : rowAt 154 = data_154 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_165 : rowAt 165 = data_165 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.1).1
theorem row_190 : rowAt 190 = data_190 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_269 : rowAt 269 = data_269 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_436 : rowAt 436 = data_436 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_445 : rowAt 445 = data_445 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_457 : rowAt 457 = data_457 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_correct.2.1).1
theorem row_463 : rowAt 463 = data_463 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_correct.2.2.2.2.2.2.2.1).1
theorem row_466 : rowAt 466 = data_466 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_correct.2.2.1).1
theorem row_471 : rowAt 471 = data_471 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_correct.2.2.2.2.2.2.2.1).1
theorem row_473 : rowAt 473 = data_473 := (OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece00_correct.2.1).1
theorem entry_476_checked : entryAt 476 = entry_476 := by
  rw [entry_chunk_23 10 (by decide)]
  decide +kernel
theorem row_476 : rowAt 476 = data_476 := by
  rw [rowAt, dif_neg (by decide : ¬ 476 < 6), entry_476_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨473, 0, 5, 3⟩ (rowAt 473)] = data_476
  rw [row_0, row_473]
  apply row_ext <;> decide +kernel
theorem entry_good_476 : EntryGood 476 := by
  unfold EntryGood
  rw [entry_476_checked]
  decide +kernel
theorem good_476 : Good (rowAt 476) := by
  rw [row_476]
  unfold Good
  decide +kernel

theorem entry_477_checked : entryAt 477 = entry_477 := by
  rw [entry_chunk_23 11 (by decide)]
  decide +kernel
theorem row_477 : rowAt 477 = data_477 := by
  rw [rowAt, dif_neg (by decide : ¬ 477 < 6), entry_477_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨154, 7, 4, 5⟩ (rowAt 154), placeRow ⟨154, 3, 4, 0⟩ (rowAt 154), placeRow ⟨471, 2, 5, 4⟩ (rowAt 471)] = data_477
  rw [row_55, row_154, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_477 : EntryGood 477 := by
  unfold EntryGood
  rw [entry_477_checked]
  decide +kernel
theorem good_477 : Good (rowAt 477) := by
  rw [row_477]
  unfold Good
  decide +kernel

theorem entry_478_checked : entryAt 478 = entry_478 := by
  rw [entry_chunk_23 12 (by decide)]
  decide +kernel
theorem row_478 : rowAt 478 = data_478 := by
  rw [rowAt, dif_neg (by decide : ¬ 478 < 6), entry_478_checked]
  change forkRow [placeRow ⟨25, 3, 4, 5⟩ (rowAt 25), placeRow ⟨165, 2, 4, 5⟩ (rowAt 165), placeRow ⟨190, 0, 7, 4⟩ (rowAt 190)] = data_478
  rw [row_25, row_165, row_190]
  apply row_ext <;> decide +kernel
theorem entry_good_478 : EntryGood 478 := by
  unfold EntryGood
  rw [entry_478_checked]
  decide +kernel
theorem good_478 : Good (rowAt 478) := by
  rw [row_478]
  unfold Good
  decide +kernel

theorem entry_479_checked : entryAt 479 = entry_479 := by
  rw [entry_chunk_23 13 (by decide)]
  decide +kernel
theorem row_479 : rowAt 479 = data_479 := by
  rw [rowAt, dif_neg (by decide : ¬ 479 < 6), entry_479_checked]
  change forkRow [placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 0, 4, 5⟩ (rowAt 443), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443)] = data_479
  rw [row_55, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_479 : EntryGood 479 := by
  unfold EntryGood
  rw [entry_479_checked]
  decide +kernel
theorem good_479 : Good (rowAt 479) := by
  rw [row_479]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 476 = data_476 ∧ Good (rowAt 476) ∧ EntryGood 476) ∧ (rowAt 477 = data_477 ∧ Good (rowAt 477) ∧ EntryGood 477) ∧ (rowAt 478 = data_478 ∧ Good (rowAt 478) ∧ EntryGood 478) ∧ (rowAt 479 = data_479 ∧ Good (rowAt 479) ∧ EntryGood 479) ∧ True := by
  exact ⟨⟨row_476, good_476, entry_good_476⟩, ⟨row_477, good_477, entry_good_477⟩, ⟨row_478, good_478, entry_good_478⟩, ⟨row_479, good_479, entry_good_479⟩, trivial⟩
