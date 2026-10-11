import Definitions.Def_Snaky35Cache19
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_29 (j : ℕ) (hj : j < 20) : entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_146 : rowAt 146 = data_146 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_199 : rowAt 199 = data_199 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.1).1
theorem row_221 : rowAt 221 = data_221 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_254 : rowAt 254 = data_254 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_278 : rowAt 278 = data_278 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_403 : rowAt 403 = data_403 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_448 : rowAt 448 = data_448 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.1).1
theorem row_456 : rowAt 456 = data_456 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.1).1
theorem row_465 : rowAt 465 = data_465 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_485 : rowAt 485 = data_485 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.1).1
theorem row_492 : rowAt 492 = data_492 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_512 : rowAt 512 = data_512 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.1).1
theorem row_554 : rowAt 554 = data_554 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_578 : rowAt 578 = data_578 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.1).1
theorem row_579 : rowAt 579 = data_579 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.1).1
theorem row_586 : rowAt 586 = data_586 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_592 : rowAt 592 = data_592 := (OAI.SnakyCertificate.MilestoneChecks.block19_group00_correct.2.2.2.1).1
theorem row_594 : rowAt 594 = data_594 := (OAI.SnakyCertificate.MilestoneChecks.block19_group00_correct.2.2.2.2.2.1).1
theorem entry_597_checked : entryAt 597 = entry_597 := by
  rw [entry_chunk_29 11 (by decide)]
  decide +kernel
theorem row_597 : rowAt 597 = data_597 := by
  rw [rowAt, dif_neg (by decide : ¬ 597 < 6), entry_597_checked]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨221, 0, 6, 4⟩ (rowAt 221), placeRow ⟨199, 3, 2, 4⟩ (rowAt 199), placeRow ⟨594, 1, 6, 5⟩ (rowAt 594)] = data_597
  rw [row_24, row_221, row_199, row_594]
  apply row_ext <;> decide +kernel
theorem entry_good_597 : EntryGood 597 := by
  unfold EntryGood
  rw [entry_597_checked]
  decide +kernel
theorem good_597 : Good (rowAt 597) := by
  rw [row_597]
  unfold Good
  decide +kernel

theorem entry_598_checked : entryAt 598 = entry_598 := by
  rw [entry_chunk_29 12 (by decide)]
  decide +kernel
theorem row_598 : rowAt 598 = data_598 := by
  rw [rowAt, dif_neg (by decide : ¬ 598 < 6), entry_598_checked]
  change forkRow [placeRow ⟨594, 0, 5, 6⟩ (rowAt 594), placeRow ⟨456, 5, 4, 2⟩ (rowAt 456), placeRow ⟨254, 1, 3, 2⟩ (rowAt 254), placeRow ⟨554, 1, 3, 2⟩ (rowAt 554), placeRow ⟨465, 0, 4, 6⟩ (rowAt 465)] = data_598
  rw [row_594, row_456, row_254, row_554, row_465]
  apply row_ext <;> decide +kernel
theorem entry_good_598 : EntryGood 598 := by
  unfold EntryGood
  rw [entry_598_checked]
  decide +kernel
theorem good_598 : Good (rowAt 598) := by
  rw [row_598]
  unfold Good
  decide +kernel

theorem entry_599_checked : entryAt 599 = entry_599 := by
  rw [entry_chunk_29 13 (by decide)]
  decide +kernel
theorem row_599 : rowAt 599 = data_599 := by
  rw [rowAt, dif_neg (by decide : ¬ 599 < 6), entry_599_checked]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (rowAt 578), placeRow ⟨492, 0, 3, 1⟩ (rowAt 492), placeRow ⟨512, 4, 3, 1⟩ (rowAt 512), placeRow ⟨586, 4, 4, 5⟩ (rowAt 586), placeRow ⟨485, 0, 5, 3⟩ (rowAt 485), placeRow ⟨579, 4, 5, 3⟩ (rowAt 579)] = data_599
  rw [row_578, row_492, row_512, row_586, row_485, row_579]
  apply row_ext <;> decide +kernel
theorem entry_good_599 : EntryGood 599 := by
  unfold EntryGood
  rw [entry_599_checked]
  decide +kernel
theorem good_599 : Good (rowAt 599) := by
  rw [row_599]
  unfold Good
  decide +kernel

theorem entry_600_checked : entryAt 600 = entry_600 := by
  rw [entry_chunk_29 14 (by decide)]
  decide +kernel
theorem row_600 : rowAt 600 = data_600 := by
  rw [rowAt, dif_neg (by decide : ¬ 600 < 6), entry_600_checked]
  change forkRow [placeRow ⟨448, 0, 4, 5⟩ (rowAt 448), placeRow ⟨278, 2, 1, 4⟩ (rowAt 278), placeRow ⟨592, 5, 5, 3⟩ (rowAt 592), placeRow ⟨403, 5, 5, 4⟩ (rowAt 403), placeRow ⟨146, 5, 4, 3⟩ (rowAt 146)] = data_600
  rw [row_448, row_278, row_592, row_403, row_146]
  apply row_ext <;> decide +kernel
theorem entry_good_600 : EntryGood 600 := by
  unfold EntryGood
  rw [entry_600_checked]
  decide +kernel
theorem good_600 : Good (rowAt 600) := by
  rw [row_600]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 597 = data_597 ∧ Good (rowAt 597) ∧ EntryGood 597) ∧ (rowAt 598 = data_598 ∧ Good (rowAt 598) ∧ EntryGood 598) ∧ (rowAt 599 = data_599 ∧ Good (rowAt 599) ∧ EntryGood 599) ∧ (rowAt 600 = data_600 ∧ Good (rowAt 600) ∧ EntryGood 600) ∧ True := by
  exact ⟨⟨row_597, good_597, entry_good_597⟩, ⟨row_598, good_598, entry_good_598⟩, ⟨row_599, good_599, entry_good_599⟩, ⟨row_600, good_600, entry_good_600⟩, trivial⟩
