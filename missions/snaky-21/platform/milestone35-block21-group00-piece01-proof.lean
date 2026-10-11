import Definitions.Def_Snaky35Cache21
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block20_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block21_group00_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_30 (j : ℕ) (hj : j < 10) : entryAt (606 + j) = tableChunk_30[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_221 : rowAt 221 = data_221 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_286 : rowAt 286 = data_286 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_370 : rowAt 370 = data_370 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_392 : rowAt 392 = data_392 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.1).1
theorem row_456 : rowAt 456 = data_456 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.1).1
theorem row_472 : rowAt 472 = data_472 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_503 : rowAt 503 = data_503 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_532 : rowAt 532 = data_532 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_542 : rowAt 542 = data_542 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_543 : rowAt 543 = data_543 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_566 : rowAt 566 = data_566 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_589 : rowAt 589 = data_589 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.1).1
theorem row_592 : rowAt 592 = data_592 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.1).1
theorem row_594 : rowAt 594 = data_594 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.1).1
theorem row_600 : rowAt 600 = data_600 := (OAI.SnakyCertificate.MilestoneChecks.block19_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_607 : rowAt 607 = data_607 := (OAI.SnakyCertificate.MilestoneChecks.block20_correct.2.2.2.2.2.2.1).1
theorem row_608 : rowAt 608 = data_608 := (OAI.SnakyCertificate.MilestoneChecks.block20_correct.2.2.2.2.2.2.2.1).1
theorem row_609 : rowAt 609 = data_609 := (OAI.SnakyCertificate.MilestoneChecks.block20_correct.2.2.2.2.2.2.2.2.1).1
theorem row_610 : rowAt 610 = data_610 := (OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.1).1
theorem row_613 : rowAt 613 = data_613 := (OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.2.2.2.1).1
theorem entry_614_checked : entryAt 614 = entry_614 := by
  rw [entry_chunk_30 8 (by decide)]
  decide +kernel
theorem row_614 : rowAt 614 = data_614 := by
  rw [rowAt, dif_neg (by decide : ¬ 614 < 6), entry_614_checked]
  change forkRow [placeRow ⟨608, 1, 7, 5⟩ (rowAt 608), placeRow ⟨543, 3, 5, 6⟩ (rowAt 543), placeRow ⟨370, 6, 3, 4⟩ (rowAt 370), placeRow ⟨392, 7, 3, 4⟩ (rowAt 392), placeRow ⟨610, 3, 5, 6⟩ (rowAt 610), placeRow ⟨600, 0, 6, 4⟩ (rowAt 600), placeRow ⟨613, 0, 6, 4⟩ (rowAt 613)] = data_614
  rw [row_608, row_543, row_370, row_392, row_610, row_600, row_613]
  apply row_ext <;> decide +kernel
theorem entry_good_614 : EntryGood 614 := by
  unfold EntryGood
  rw [entry_614_checked]
  decide +kernel
theorem good_614 : Good (rowAt 614) := by
  rw [row_614]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 614 = data_614 ∧ Good (rowAt 614) ∧ EntryGood 614) ∧ True := by
  exact ⟨⟨row_614, good_614, entry_good_614⟩, trivial⟩
