import Definitions.Def_Snaky35Cache20
import Solutions.SnakyMilestones.Certificate35Part19
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
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


theorem block20_group00_piece00_correct : (rowAt 601 = data_601 ∧ Good (rowAt 601) ∧ EntryGood 601) ∧ (rowAt 602 = data_602 ∧ Good (rowAt 602) ∧ EntryGood 602) ∧ (rowAt 603 = data_603 ∧ Good (rowAt 603) ∧ EntryGood 603) ∧ (rowAt 604 = data_604 ∧ Good (rowAt 604) ∧ EntryGood 604) ∧ True := by
  exact ⟨⟨row_601, good_601, entry_good_601⟩, ⟨row_602, good_602, entry_good_602⟩, ⟨row_603, good_603, entry_good_603⟩, ⟨row_604, good_604, entry_good_604⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
