import Definitions.Def_Snaky35Cache01
import Solutions.SnakyMilestones.Certificate35Block01Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_56_checked : entryAt 56 = entry_56 := by
  rw [entry_chunk_2 10 (by decide)]
  decide +kernel
theorem row_56 : rowAt 56 = data_56 := by
  rw [rowAt, dif_neg (by decide : ¬ 56 < 6), entry_56_checked]
  change forkRow [placeRow ⟨7, 4, 0, 5⟩ (rowAt 7), placeRow ⟨7, 6, 0, 3⟩ (rowAt 7)] = data_56
  rw [row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_56 : EntryGood 56 := by
  unfold EntryGood
  rw [entry_56_checked]
  decide +kernel
theorem good_56 : Good (rowAt 56) := by
  rw [row_56]
  unfold Good
  decide +kernel

theorem entry_57_checked : entryAt 57 = entry_57 := by
  rw [entry_chunk_2 11 (by decide)]
  decide +kernel
theorem row_57 : rowAt 57 = data_57 := by
  rw [rowAt, dif_neg (by decide : ¬ 57 < 6), entry_57_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_57
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_57 : EntryGood 57 := by
  unfold EntryGood
  rw [entry_57_checked]
  decide +kernel
theorem good_57 : Good (rowAt 57) := by
  rw [row_57]
  unfold Good
  decide +kernel

theorem entry_58_checked : entryAt 58 = entry_58 := by
  rw [entry_chunk_2 12 (by decide)]
  decide +kernel
theorem row_58 : rowAt 58 = data_58 := by
  rw [rowAt, dif_neg (by decide : ¬ 58 < 6), entry_58_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨7, 0, 4, 5⟩ (rowAt 7)] = data_58
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_58 : EntryGood 58 := by
  unfold EntryGood
  rw [entry_58_checked]
  decide +kernel
theorem good_58 : Good (rowAt 58) := by
  rw [row_58]
  unfold Good
  decide +kernel

theorem entry_59_checked : entryAt 59 = entry_59 := by
  rw [entry_chunk_2 13 (by decide)]
  decide +kernel
theorem row_59 : rowAt 59 = data_59 := by
  rw [rowAt, dif_neg (by decide : ¬ 59 < 6), entry_59_checked]
  change forkRow [placeRow ⟨0, 6, 5, 4⟩ (rowAt 0), placeRow ⟨7, 4, 0, 5⟩ (rowAt 7)] = data_59
  rw [row_0, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_59 : EntryGood 59 := by
  unfold EntryGood
  rw [entry_59_checked]
  decide +kernel
theorem good_59 : Good (rowAt 59) := by
  rw [row_59]
  unfold Good
  decide +kernel


theorem block01_group03_piece00_correct : (rowAt 56 = data_56 ∧ Good (rowAt 56) ∧ EntryGood 56) ∧ (rowAt 57 = data_57 ∧ Good (rowAt 57) ∧ EntryGood 57) ∧ (rowAt 58 = data_58 ∧ Good (rowAt 58) ∧ EntryGood 58) ∧ (rowAt 59 = data_59 ∧ Good (rowAt 59) ∧ EntryGood 59) ∧ True := by
  exact ⟨⟨row_56, good_56, entry_good_56⟩, ⟨row_57, good_57, entry_good_57⟩, ⟨row_58, good_58, entry_good_58⟩, ⟨row_59, good_59, entry_good_59⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
