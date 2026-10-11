import Definitions.Def_Snaky35Cache01
import Solutions.SnakyMilestones.Certificate35Block01Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_40_checked : entryAt 40 = entry_40 := by
  rw [entry_chunk_1 14 (by decide)]
  decide +kernel
theorem row_40 : rowAt 40 = data_40 := by
  rw [rowAt, dif_neg (by decide : ¬ 40 < 6), entry_40_checked]
  change forkRow [placeRow ⟨3, 0, 4, 3⟩ (rowAt 3), placeRow ⟨16, 0, 3, 4⟩ (rowAt 16)] = data_40
  rw [row_3, row_16]
  apply row_ext <;> decide +kernel
theorem entry_good_40 : EntryGood 40 := by
  unfold EntryGood
  rw [entry_40_checked]
  decide +kernel
theorem good_40 : Good (rowAt 40) := by
  rw [row_40]
  unfold Good
  decide +kernel

theorem entry_41_checked : entryAt 41 = entry_41 := by
  rw [entry_chunk_1 15 (by decide)]
  decide +kernel
theorem row_41 : rowAt 41 = data_41 := by
  rw [rowAt, dif_neg (by decide : ¬ 41 < 6), entry_41_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨1, 4, 6, 3⟩ (rowAt 1)] = data_41
  rw [row_6, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_41 : EntryGood 41 := by
  unfold EntryGood
  rw [entry_41_checked]
  decide +kernel
theorem good_41 : Good (rowAt 41) := by
  rw [row_41]
  unfold Good
  decide +kernel

theorem entry_42_checked : entryAt 42 = entry_42 := by
  rw [entry_chunk_1 16 (by decide)]
  decide +kernel
theorem row_42 : rowAt 42 = data_42 := by
  rw [rowAt, dif_neg (by decide : ¬ 42 < 6), entry_42_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨6, 4, 1, 5⟩ (rowAt 6)] = data_42
  rw [row_0, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_42 : EntryGood 42 := by
  unfold EntryGood
  rw [entry_42_checked]
  decide +kernel
theorem good_42 : Good (rowAt 42) := by
  rw [row_42]
  unfold Good
  decide +kernel

theorem entry_43_checked : entryAt 43 = entry_43 := by
  rw [entry_chunk_1 17 (by decide)]
  decide +kernel
theorem row_43 : rowAt 43 = data_43 := by
  rw [rowAt, dif_neg (by decide : ¬ 43 < 6), entry_43_checked]
  change forkRow [placeRow ⟨2, 4, 5, 3⟩ (rowAt 2), placeRow ⟨6, 3, 3, 5⟩ (rowAt 6)] = data_43
  rw [row_2, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_43 : EntryGood 43 := by
  unfold EntryGood
  rw [entry_43_checked]
  decide +kernel
theorem good_43 : Good (rowAt 43) := by
  rw [row_43]
  unfold Good
  decide +kernel


theorem block01_group01_piece00_correct : (rowAt 40 = data_40 ∧ Good (rowAt 40) ∧ EntryGood 40) ∧ (rowAt 41 = data_41 ∧ Good (rowAt 41) ∧ EntryGood 41) ∧ (rowAt 42 = data_42 ∧ Good (rowAt 42) ∧ EntryGood 42) ∧ (rowAt 43 = data_43 ∧ Good (rowAt 43) ∧ EntryGood 43) ∧ True := by
  exact ⟨⟨row_40, good_40, entry_good_40⟩, ⟨row_41, good_41, entry_good_41⟩, ⟨row_42, good_42, entry_good_42⟩, ⟨row_43, good_43, entry_good_43⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
