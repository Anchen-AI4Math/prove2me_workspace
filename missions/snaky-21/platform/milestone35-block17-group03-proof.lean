import Definitions.Def_Snaky35Cache17
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_28 (j : ℕ) (hj : j < 20) : entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_34 : rowAt 34 = data_34 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.1).1
theorem row_275 : rowAt 275 = data_275 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_330 : rowAt 330 = data_330 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_538 : rowAt 538 = data_538 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_547 : rowAt 547 = data_547 := (OAI.SnakyCertificate.MilestoneChecks.block17_group00_correct.2.2.2.1).1
theorem row_565 : rowAt 565 = data_565 := (OAI.SnakyCertificate.MilestoneChecks.block17_group02_correct.2.2.2.2.2.1).1
theorem entry_568_checked : entryAt 568 = entry_568 := by
  rw [entry_chunk_28 2 (by decide)]
  decide +kernel
theorem row_568 : rowAt 568 = data_568 := by
  rw [rowAt, dif_neg (by decide : ¬ 568 < 6), entry_568_checked]
  change forkRow [placeRow ⟨538, 4, 6, 4⟩ (rowAt 538), placeRow ⟨547, 0, 2, 4⟩ (rowAt 547), placeRow ⟨275, 0, 6, 4⟩ (rowAt 275), placeRow ⟨565, 0, 2, 4⟩ (rowAt 565), placeRow ⟨330, 0, 6, 4⟩ (rowAt 330)] = data_568
  rw [row_538, row_547, row_275, row_565, row_330]
  apply row_ext <;> decide +kernel
theorem entry_good_568 : EntryGood 568 := by
  unfold EntryGood
  rw [entry_568_checked]
  decide +kernel
theorem good_568 : Good (rowAt 568) := by
  rw [row_568]
  unfold Good
  decide +kernel

theorem entry_569_checked : entryAt 569 = entry_569 := by
  rw [entry_chunk_28 3 (by decide)]
  decide +kernel
theorem row_569 : rowAt 569 = data_569 := by
  rw [rowAt, dif_neg (by decide : ¬ 569 < 6), entry_569_checked]
  change forkRow [placeRow ⟨34, 3, 4, 2⟩ (rowAt 34), placeRow ⟨568, 4, 5, 4⟩ (rowAt 568)] = data_569
  rw [row_34, row_568]
  apply row_ext <;> decide +kernel
theorem entry_good_569 : EntryGood 569 := by
  unfold EntryGood
  rw [entry_569_checked]
  decide +kernel
theorem good_569 : Good (rowAt 569) := by
  rw [row_569]
  unfold Good
  decide +kernel

theorem entry_570_checked : entryAt 570 = entry_570 := by
  rw [entry_chunk_28 4 (by decide)]
  decide +kernel
theorem row_570 : rowAt 570 = data_570 := by
  rw [rowAt, dif_neg (by decide : ¬ 570 < 6), entry_570_checked]
  change forkRow [placeRow ⟨569, 0, 2, 5⟩ (rowAt 569), placeRow ⟨2, 7, 4, 3⟩ (rowAt 2)] = data_570
  rw [row_569, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_570 : EntryGood 570 := by
  unfold EntryGood
  rw [entry_570_checked]
  decide +kernel
theorem good_570 : Good (rowAt 570) := by
  rw [row_570]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 568 = data_568 ∧ Good (rowAt 568) ∧ EntryGood 568) ∧ (rowAt 569 = data_569 ∧ Good (rowAt 569) ∧ EntryGood 569) ∧ (rowAt 570 = data_570 ∧ Good (rowAt 570) ∧ EntryGood 570) ∧ True := by
  exact ⟨⟨row_568, good_568, entry_good_568⟩, ⟨row_569, good_569, entry_good_569⟩, ⟨row_570, good_570, entry_good_570⟩, trivial⟩
