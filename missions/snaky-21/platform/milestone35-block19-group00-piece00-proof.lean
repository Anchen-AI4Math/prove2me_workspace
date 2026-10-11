import Definitions.Def_Snaky35Cache19
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_29 (j : ℕ) (hj : j < 20) : entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_30 : rowAt 30 = data_30 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_217 : rowAt 217 = data_217 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_330 : rowAt 330 = data_330 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_385 : rowAt 385 = data_385 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.1).1
theorem row_406 : rowAt 406 = data_406 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_411 : rowAt 411 = data_411 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_460 : rowAt 460 = data_460 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_476 : rowAt 476 = data_476 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_490 : rowAt 490 = data_490 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_524 : rowAt 524 = data_524 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_529 : rowAt 529 = data_529 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_538 : rowAt 538 = data_538 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_551 : rowAt 551 = data_551 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.1).1
theorem row_572 : rowAt 572 = data_572 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.1).1
theorem row_577 : rowAt 577 = data_577 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.1).1
theorem row_586 : rowAt 586 = data_586 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_588 : rowAt 588 = data_588 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_589_checked : entryAt 589 = entry_589 := by
  rw [entry_chunk_29 3 (by decide)]
  decide +kernel
theorem row_589 : rowAt 589 = data_589 := by
  rw [rowAt, dif_neg (by decide : ¬ 589 < 6), entry_589_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_589
  rw [row_4, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_589 : EntryGood 589 := by
  unfold EntryGood
  rw [entry_589_checked]
  decide +kernel
theorem good_589 : Good (rowAt 589) := by
  rw [row_589]
  unfold Good
  decide +kernel

theorem entry_590_checked : entryAt 590 = entry_590 := by
  rw [entry_chunk_29 4 (by decide)]
  decide +kernel
theorem row_590 : rowAt 590 = data_590 := by
  rw [rowAt, dif_neg (by decide : ¬ 590 < 6), entry_590_checked]
  change forkRow [placeRow ⟨295, 7, 4, 3⟩ (rowAt 295), placeRow ⟨173, 7, 4, 3⟩ (rowAt 173), placeRow ⟨577, 0, 4, 7⟩ (rowAt 577), placeRow ⟨490, 0, 4, 7⟩ (rowAt 490), placeRow ⟨217, 5, 4, 3⟩ (rowAt 217)] = data_590
  rw [row_295, row_173, row_577, row_490, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_590 : EntryGood 590 := by
  unfold EntryGood
  rw [entry_590_checked]
  decide +kernel
theorem good_590 : Good (rowAt 590) := by
  rw [row_590]
  unfold Good
  decide +kernel

theorem entry_591_checked : entryAt 591 = entry_591 := by
  rw [entry_chunk_29 5 (by decide)]
  decide +kernel
theorem row_591 : rowAt 591 = data_591 := by
  rw [rowAt, dif_neg (by decide : ¬ 591 < 6), entry_591_checked]
  change forkRow [placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨529, 1, 4, 1⟩ (rowAt 529), placeRow ⟨529, 3, 4, 1⟩ (rowAt 529), placeRow ⟨538, 1, 4, 1⟩ (rowAt 538), placeRow ⟨538, 3, 4, 1⟩ (rowAt 538), placeRow ⟨197, 5, 4, 1⟩ (rowAt 197)] = data_591
  rw [row_524, row_529, row_538, row_197]
  apply row_ext <;> decide +kernel
theorem entry_good_591 : EntryGood 591 := by
  unfold EntryGood
  rw [entry_591_checked]
  decide +kernel
theorem good_591 : Good (rowAt 591) := by
  rw [row_591]
  unfold Good
  decide +kernel

theorem entry_592_checked : entryAt 592 = entry_592 := by
  rw [entry_chunk_29 6 (by decide)]
  decide +kernel
theorem row_592 : rowAt 592 = data_592 := by
  rw [rowAt, dif_neg (by decide : ¬ 592 < 6), entry_592_checked]
  change forkRow [placeRow ⟨588, 0, 4, 5⟩ (rowAt 588), placeRow ⟨108, 7, 3, 0⟩ (rowAt 108)] = data_592
  rw [row_588, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_592 : EntryGood 592 := by
  unfold EntryGood
  rw [entry_592_checked]
  decide +kernel
theorem good_592 : Good (rowAt 592) := by
  rw [row_592]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 589 = data_589 ∧ Good (rowAt 589) ∧ EntryGood 589) ∧ (rowAt 590 = data_590 ∧ Good (rowAt 590) ∧ EntryGood 590) ∧ (rowAt 591 = data_591 ∧ Good (rowAt 591) ∧ EntryGood 591) ∧ (rowAt 592 = data_592 ∧ Good (rowAt 592) ∧ EntryGood 592) ∧ True := by
  exact ⟨⟨row_589, good_589, entry_good_589⟩, ⟨row_590, good_590, entry_good_590⟩, ⟨row_591, good_591, entry_good_591⟩, ⟨row_592, good_592, entry_good_592⟩, trivial⟩
