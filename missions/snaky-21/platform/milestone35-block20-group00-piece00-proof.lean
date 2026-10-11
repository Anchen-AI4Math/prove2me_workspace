import Definitions.Def_Snaky35Cache20
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_29 (j : ℕ) (hj : j < 20) : entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_30 (j : ℕ) (hj : j < 10) : entryAt (606 + j) = tableChunk_30[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_119 : rowAt 119 = data_119 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_123 : rowAt 123 = data_123 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_274 : rowAt 274 = data_274 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_350 : rowAt 350 = data_350 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_375 : rowAt 375 = data_375 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_383 : rowAt 383 = data_383 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_400 : rowAt 400 = data_400 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_419 : rowAt 419 = data_419 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.1).1
theorem row_420 : rowAt 420 = data_420 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.1).1
theorem row_437 : rowAt 437 = data_437 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_467 : rowAt 467 = data_467 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_469 : rowAt 469 = data_469 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_486 : rowAt 486 = data_486 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.1).1
theorem row_505 : rowAt 505 = data_505 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_515 : rowAt 515 = data_515 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.1).1
theorem row_520 : rowAt 520 = data_520 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.1).1
theorem row_521 : rowAt 521 = data_521 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_522 : rowAt 522 = data_522 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_530 : rowAt 530 = data_530 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_531 : rowAt 531 = data_531 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_533 : rowAt 533 = data_533 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_537 : rowAt 537 = data_537 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_550 : rowAt 550 = data_550 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.1).1
theorem row_551 : rowAt 551 = data_551 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.1).1
theorem row_553 : rowAt 553 = data_553 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_571 : rowAt 571 = data_571 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.1).1
theorem row_573 : rowAt 573 = data_573 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.1).1
theorem row_580 : rowAt 580 = data_580 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_581 : rowAt 581 = data_581 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_585 : rowAt 585 = data_585 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_586 : rowAt 586 = data_586 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_589 : rowAt 589 = data_589 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.1).1
theorem row_592 : rowAt 592 = data_592 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.1).1
theorem row_593 : rowAt 593 = data_593 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.1).1
theorem row_596 : rowAt 596 = data_596 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.2.2.1).1
theorem row_597 : rowAt 597 = data_597 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.2.2.2.1).1
theorem row_598 : rowAt 598 = data_598 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_599 : rowAt 599 = data_599 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_601_checked : entryAt 601 = entry_601 := by
  rw [entry_chunk_29 15 (by decide)]
  decide +kernel
theorem row_601 : rowAt 601 = data_601 := by
  rw [rowAt, dif_neg (by decide : ¬ 601 < 6), entry_601_checked]
  change forkRow [placeRow ⟨437, 6, 4, 1⟩ (rowAt 437), placeRow ⟨553, 0, 4, 5⟩ (rowAt 553), placeRow ⟨592, 0, 5, 5⟩ (rowAt 592), placeRow ⟨236, 4, 3, 5⟩ (rowAt 236), placeRow ⟨469, 4, 4, 1⟩ (rowAt 469)] = data_601
  rw [row_437, row_553, row_592, row_236, row_469]
  apply row_ext <;> decide +kernel
theorem entry_good_601 : EntryGood 601 := by
  unfold EntryGood
  rw [entry_601_checked]
  decide +kernel
theorem good_601 : Good (rowAt 601) := by
  rw [row_601]
  unfold Good
  decide +kernel

theorem entry_602_checked : entryAt 602 = entry_602 := by
  rw [entry_chunk_29 16 (by decide)]
  decide +kernel
theorem row_602 : rowAt 602 = data_602 := by
  rw [rowAt, dif_neg (by decide : ¬ 602 < 6), entry_602_checked]
  change forkRow [placeRow ⟨553, 0, 4, 7⟩ (rowAt 553), placeRow ⟨467, 4, 4, 3⟩ (rowAt 467), placeRow ⟨592, 0, 5, 7⟩ (rowAt 592), placeRow ⟨437, 6, 4, 3⟩ (rowAt 437), placeRow ⟨236, 4, 3, 7⟩ (rowAt 236)] = data_602
  rw [row_553, row_467, row_592, row_437, row_236]
  apply row_ext <;> decide +kernel
theorem entry_good_602 : EntryGood 602 := by
  unfold EntryGood
  rw [entry_602_checked]
  decide +kernel
theorem good_602 : Good (rowAt 602) := by
  rw [row_602]
  unfold Good
  decide +kernel

theorem entry_603_checked : entryAt 603 = entry_603 := by
  rw [entry_chunk_29 17 (by decide)]
  decide +kernel
theorem row_603 : rowAt 603 = data_603 := by
  rw [rowAt, dif_neg (by decide : ¬ 603 < 6), entry_603_checked]
  change forkRow [placeRow ⟨505, 1, 5, 4⟩ (rowAt 505), placeRow ⟨505, 5, 5, 4⟩ (rowAt 505), placeRow ⟨586, 5, 5, 4⟩ (rowAt 586), placeRow ⟨551, 7, 5, 4⟩ (rowAt 551), placeRow ⟨531, 6, 4, 2⟩ (rowAt 531), placeRow ⟨586, 1, 5, 4⟩ (rowAt 586), placeRow ⟨585, 1, 5, 4⟩ (rowAt 585), placeRow ⟨585, 5, 5, 4⟩ (rowAt 585), placeRow ⟨551, 3, 5, 4⟩ (rowAt 551), placeRow ⟨573, 1, 5, 4⟩ (rowAt 573), placeRow ⟨533, 5, 5, 4⟩ (rowAt 533), placeRow ⟨533, 1, 5, 4⟩ (rowAt 533)] = data_603
  rw [row_505, row_586, row_551, row_531, row_585, row_573, row_533]
  apply row_ext <;> decide +kernel
theorem entry_good_603 : EntryGood 603 := by
  unfold EntryGood
  rw [entry_603_checked]
  decide +kernel
theorem good_603 : Good (rowAt 603) := by
  rw [row_603]
  unfold Good
  decide +kernel

theorem entry_604_checked : entryAt 604 = entry_604 := by
  rw [entry_chunk_29 18 (by decide)]
  decide +kernel
theorem row_604 : rowAt 604 = data_604 := by
  rw [rowAt, dif_neg (by decide : ¬ 604 < 6), entry_604_checked]
  change forkRow [placeRow ⟨597, 0, 3, 4⟩ (rowAt 597), placeRow ⟨375, 2, 4, 3⟩ (rowAt 375), placeRow ⟨597, 1, 4, 3⟩ (rowAt 597), placeRow ⟨375, 3, 3, 4⟩ (rowAt 375), placeRow ⟨350, 3, 4, 3⟩ (rowAt 350), placeRow ⟨350, 2, 3, 4⟩ (rowAt 350)] = data_604
  rw [row_597, row_375, row_350]
  apply row_ext <;> decide +kernel
theorem entry_good_604 : EntryGood 604 := by
  unfold EntryGood
  rw [entry_604_checked]
  decide +kernel
theorem good_604 : Good (rowAt 604) := by
  rw [row_604]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 601 = data_601 ∧ Good (rowAt 601) ∧ EntryGood 601) ∧ (rowAt 602 = data_602 ∧ Good (rowAt 602) ∧ EntryGood 602) ∧ (rowAt 603 = data_603 ∧ Good (rowAt 603) ∧ EntryGood 603) ∧ (rowAt 604 = data_604 ∧ Good (rowAt 604) ∧ EntryGood 604) ∧ True := by
  exact ⟨⟨row_601, good_601, entry_good_601⟩, ⟨row_602, good_602, entry_good_602⟩, ⟨row_603, good_603, entry_good_603⟩, ⟨row_604, good_604, entry_good_604⟩, trivial⟩
