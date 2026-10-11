import Definitions.Def_Snaky35Cache13
import Solutions.SnakyMilestones.Certificate35Block13Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_440_checked : entryAt 440 = entry_440 := by
  rw [entry_chunk_21 14 (by decide)]
  decide +kernel
theorem row_440 : rowAt 440 = data_440 := by
  rw [rowAt, dif_neg (by decide : ¬ 440 < 6), entry_440_checked]
  change forkRow [placeRow ⟨6, 6, 1, 3⟩ (rowAt 6), placeRow ⟨435, 0, 2, 5⟩ (rowAt 435)] = data_440
  rw [row_6, row_435]
  apply row_ext <;> decide +kernel
theorem entry_good_440 : EntryGood 440 := by
  unfold EntryGood
  rw [entry_440_checked]
  decide +kernel
theorem good_440 : Good (rowAt 440) := by
  rw [row_440]
  unfold Good
  decide +kernel

theorem entry_441_checked : entryAt 441 = entry_441 := by
  rw [entry_chunk_21 15 (by decide)]
  decide +kernel
theorem row_441 : rowAt 441 = data_441 := by
  rw [rowAt, dif_neg (by decide : ¬ 441 < 6), entry_441_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨435, 0, 4, 6⟩ (rowAt 435)] = data_441
  rw [row_6, row_435]
  apply row_ext <;> decide +kernel
theorem entry_good_441 : EntryGood 441 := by
  unfold EntryGood
  rw [entry_441_checked]
  decide +kernel
theorem good_441 : Good (rowAt 441) := by
  rw [row_441]
  unfold Good
  decide +kernel

theorem entry_442_checked : entryAt 442 = entry_442 := by
  rw [entry_chunk_21 16 (by decide)]
  decide +kernel
theorem row_442 : rowAt 442 = data_442 := by
  rw [rowAt, dif_neg (by decide : ¬ 442 < 6), entry_442_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨433, 0, 4, 5⟩ (rowAt 433), placeRow ⟨201, 0, 3, 2⟩ (rowAt 201)] = data_442
  rw [row_63, row_7, row_433, row_201]
  apply row_ext <;> decide +kernel
theorem entry_good_442 : EntryGood 442 := by
  unfold EntryGood
  rw [entry_442_checked]
  decide +kernel
theorem good_442 : Good (rowAt 442) := by
  rw [row_442]
  unfold Good
  decide +kernel

theorem entry_443_checked : entryAt 443 = entry_443 := by
  rw [entry_chunk_21 17 (by decide)]
  decide +kernel
theorem row_443 : rowAt 443 = data_443 := by
  rw [rowAt, dif_neg (by decide : ¬ 443 < 6), entry_443_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨438, 0, 3, 4⟩ (rowAt 438)] = data_443
  rw [row_6, row_438]
  apply row_ext <;> decide +kernel
theorem entry_good_443 : EntryGood 443 := by
  unfold EntryGood
  rw [entry_443_checked]
  decide +kernel
theorem good_443 : Good (rowAt 443) := by
  rw [row_443]
  unfold Good
  decide +kernel


theorem block13_group03_piece00_correct : (rowAt 440 = data_440 ∧ Good (rowAt 440) ∧ EntryGood 440) ∧ (rowAt 441 = data_441 ∧ Good (rowAt 441) ∧ EntryGood 441) ∧ (rowAt 442 = data_442 ∧ Good (rowAt 442) ∧ EntryGood 442) ∧ (rowAt 443 = data_443 ∧ Good (rowAt 443) ∧ EntryGood 443) ∧ True := by
  exact ⟨⟨row_440, good_440, entry_good_440⟩, ⟨row_441, good_441, entry_good_441⟩, ⟨row_442, good_442, entry_good_442⟩, ⟨row_443, good_443, entry_good_443⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
