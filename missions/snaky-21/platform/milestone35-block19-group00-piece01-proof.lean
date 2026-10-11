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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_group00_piece00_correct
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
theorem row_592 : rowAt 592 = data_592 := (OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece00_correct.2.2.2.1).1
theorem entry_593_checked : entryAt 593 = entry_593 := by
  rw [entry_chunk_29 7 (by decide)]
  decide +kernel
theorem row_593 : rowAt 593 = data_593 := by
  rw [rowAt, dif_neg (by decide : ¬ 593 < 6), entry_593_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_593
  rw [row_2, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_593 : EntryGood 593 := by
  unfold EntryGood
  rw [entry_593_checked]
  decide +kernel
theorem good_593 : Good (rowAt 593) := by
  rw [row_593]
  unfold Good
  decide +kernel

theorem entry_594_checked : entryAt 594 = entry_594 := by
  rw [entry_chunk_29 8 (by decide)]
  decide +kernel
theorem row_594 : rowAt 594 = data_594 := by
  rw [rowAt, dif_neg (by decide : ¬ 594 < 6), entry_594_checked]
  change forkRow [placeRow ⟨30, 1, 4, 3⟩ (rowAt 30), placeRow ⟨476, 1, 4, 3⟩ (rowAt 476), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_594
  rw [row_30, row_476, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_594 : EntryGood 594 := by
  unfold EntryGood
  rw [entry_594_checked]
  decide +kernel
theorem good_594 : Good (rowAt 594) := by
  rw [row_594]
  unfold Good
  decide +kernel

theorem entry_595_checked : entryAt 595 = entry_595 := by
  rw [entry_chunk_29 9 (by decide)]
  decide +kernel
theorem row_595 : rowAt 595 = data_595 := by
  rw [rowAt, dif_neg (by decide : ¬ 595 < 6), entry_595_checked]
  change forkRow [placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨586, 1, 5, 4⟩ (rowAt 586), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨551, 1, 2, 4⟩ (rowAt 551), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406), placeRow ⟨572, 0, 2, 4⟩ (rowAt 572)] = data_595
  rw [row_460, row_586, row_411, row_551, row_406, row_572]
  apply row_ext <;> decide +kernel
theorem entry_good_595 : EntryGood 595 := by
  unfold EntryGood
  rw [entry_595_checked]
  decide +kernel
theorem good_595 : Good (rowAt 595) := by
  rw [row_595]
  unfold Good
  decide +kernel

theorem entry_596_checked : entryAt 596 = entry_596 := by
  rw [entry_chunk_29 10 (by decide)]
  decide +kernel
theorem row_596 : rowAt 596 = data_596 := by
  rw [rowAt, dif_neg (by decide : ¬ 596 < 6), entry_596_checked]
  change forkRow [placeRow ⟨385, 5, 4, 2⟩ (rowAt 385), placeRow ⟨592, 0, 5, 6⟩ (rowAt 592), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330), placeRow ⟨529, 5, 4, 6⟩ (rowAt 529), placeRow ⟨385, 1, 4, 6⟩ (rowAt 385), placeRow ⟨330, 5, 4, 2⟩ (rowAt 330)] = data_596
  rw [row_385, row_592, row_330, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_596 : EntryGood 596 := by
  unfold EntryGood
  rw [entry_596_checked]
  decide +kernel
theorem good_596 : Good (rowAt 596) := by
  rw [row_596]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 593 = data_593 ∧ Good (rowAt 593) ∧ EntryGood 593) ∧ (rowAt 594 = data_594 ∧ Good (rowAt 594) ∧ EntryGood 594) ∧ (rowAt 595 = data_595 ∧ Good (rowAt 595) ∧ EntryGood 595) ∧ (rowAt 596 = data_596 ∧ Good (rowAt 596) ∧ EntryGood 596) ∧ True := by
  exact ⟨⟨row_593, good_593, entry_good_593⟩, ⟨row_594, good_594, entry_good_594⟩, ⟨row_595, good_595, entry_good_595⟩, ⟨row_596, good_596, entry_good_596⟩, trivial⟩
