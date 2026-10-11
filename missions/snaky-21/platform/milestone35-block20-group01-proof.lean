import Definitions.Def_Snaky35Cache20
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block20_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_30 (j : ℕ) (hj : j < 10) : entryAt (606 + j) = tableChunk_30[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_221 : rowAt 221 = data_221 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_286 : rowAt 286 = data_286 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_532 : rowAt 532 = data_532 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_542 : rowAt 542 = data_542 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_562 : rowAt 562 = data_562 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_575 : rowAt 575 = data_575 := (OAI.SnakyCertificate.MilestoneChecks.block18_correct.2.2.2.2.1).1
theorem row_604 : rowAt 604 = data_604 := (OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.1).1
theorem entry_609_checked : entryAt 609 = entry_609 := by
  rw [entry_chunk_30 3 (by decide)]
  decide +kernel
theorem row_609 : rowAt 609 = data_609 := by
  rw [rowAt, dif_neg (by decide : ¬ 609 < 6), entry_609_checked]
  change forkRow [placeRow ⟨286, 4, 4, 5⟩ (rowAt 286), placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨532, 4, 4, 5⟩ (rowAt 532), placeRow ⟨542, 0, 4, 5⟩ (rowAt 542), placeRow ⟨221, 3, 4, 5⟩ (rowAt 221), placeRow ⟨562, 4, 4, 5⟩ (rowAt 562), placeRow ⟨575, 4, 4, 5⟩ (rowAt 575), placeRow ⟨604, 1, 6, 4⟩ (rowAt 604)] = data_609
  rw [row_286, row_107, row_532, row_542, row_221, row_562, row_575, row_604]
  apply row_ext <;> decide +kernel
theorem entry_good_609 : EntryGood 609 := by
  unfold EntryGood
  rw [entry_609_checked]
  decide +kernel
theorem good_609 : Good (rowAt 609) := by
  rw [row_609]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 609 = data_609 ∧ Good (rowAt 609) ∧ EntryGood 609) ∧ True := by
  exact ⟨⟨row_609, good_609, entry_good_609⟩, trivial⟩
