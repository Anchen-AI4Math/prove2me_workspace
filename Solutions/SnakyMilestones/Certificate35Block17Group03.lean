import Definitions.Def_Snaky35Cache17
import Solutions.SnakyMilestones.Certificate35Block17Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
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

theorem block17_group03_correct : (rowAt 568 = data_568 ∧ Good (rowAt 568) ∧ EntryGood 568) ∧ (rowAt 569 = data_569 ∧ Good (rowAt 569) ∧ EntryGood 569) ∧ (rowAt 570 = data_570 ∧ Good (rowAt 570) ∧ EntryGood 570) ∧ True := by
  exact ⟨⟨row_568, good_568, entry_good_568⟩, ⟨row_569, good_569, entry_good_569⟩, ⟨row_570, good_570, entry_good_570⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
