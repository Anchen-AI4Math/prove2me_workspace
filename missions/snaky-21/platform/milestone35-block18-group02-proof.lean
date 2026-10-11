import Definitions.Def_Snaky35Cache18
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_29 (j : ℕ) (hj : j < 20) : entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_467 : rowAt 467 = data_467 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_477 : rowAt 477 = data_477 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_479 : rowAt 479 = data_479 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_586 : rowAt 586 = data_586 := (OAI.SnakyCertificate.MilestoneChecks.block18_group01_correct.2.2.2.2.2.2.2.1).1
theorem entry_587_checked : entryAt 587 = entry_587 := by
  rw [entry_chunk_29 1 (by decide)]
  decide +kernel
theorem row_587 : rowAt 587 = data_587 := by
  rw [rowAt, dif_neg (by decide : ¬ 587 < 6), entry_587_checked]
  change forkRow [placeRow ⟨300, 2, 4, 1⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨319, 3, 5, 5⟩ (rowAt 319), placeRow ⟨477, 6, 4, 1⟩ (rowAt 477), placeRow ⟨252, 3, 4, 5⟩ (rowAt 252), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467)] = data_587
  rw [row_300, row_479, row_319, row_477, row_252, row_467]
  apply row_ext <;> decide +kernel
theorem entry_good_587 : EntryGood 587 := by
  unfold EntryGood
  rw [entry_587_checked]
  decide +kernel
theorem good_587 : Good (rowAt 587) := by
  rw [row_587]
  unfold Good
  decide +kernel

theorem entry_588_checked : entryAt 588 = entry_588 := by
  rw [entry_chunk_29 2 (by decide)]
  decide +kernel
theorem row_588 : rowAt 588 = data_588 := by
  rw [rowAt, dif_neg (by decide : ¬ 588 < 6), entry_588_checked]
  change forkRow [placeRow ⟨3, 1, 3, 3⟩ (rowAt 3), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_588
  rw [row_3, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_588 : EntryGood 588 := by
  unfold EntryGood
  rw [entry_588_checked]
  decide +kernel
theorem good_588 : Good (rowAt 588) := by
  rw [row_588]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 587 = data_587 ∧ Good (rowAt 587) ∧ EntryGood 587) ∧ (rowAt 588 = data_588 ∧ Good (rowAt 588) ∧ EntryGood 588) ∧ True := by
  exact ⟨⟨row_587, good_587, entry_good_587⟩, ⟨row_588, good_588, entry_good_588⟩, trivial⟩
