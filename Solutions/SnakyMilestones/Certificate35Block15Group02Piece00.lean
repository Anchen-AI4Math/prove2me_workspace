import Definitions.Def_Snaky35Cache15
import Solutions.SnakyMilestones.Certificate35Block15Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_496_checked : entryAt 496 = entry_496 := by
  rw [entry_chunk_24 10 (by decide)]
  decide +kernel
theorem row_496 : rowAt 496 = data_496 := by
  rw [rowAt, dif_neg (by decide : ¬ 496 < 6), entry_496_checked]
  change forkRow [placeRow ⟨25, 0, 7, 5⟩ (rowAt 25), placeRow ⟨107, 6, 3, 4⟩ (rowAt 107), placeRow ⟨163, 6, 3, 4⟩ (rowAt 163), placeRow ⟨494, 0, 7, 4⟩ (rowAt 494)] = data_496
  rw [row_25, row_107, row_163, row_494]
  apply row_ext <;> decide +kernel
theorem entry_good_496 : EntryGood 496 := by
  unfold EntryGood
  rw [entry_496_checked]
  decide +kernel
theorem good_496 : Good (rowAt 496) := by
  rw [row_496]
  unfold Good
  decide +kernel

theorem entry_497_checked : entryAt 497 = entry_497 := by
  rw [entry_chunk_24 11 (by decide)]
  decide +kernel
theorem row_497 : rowAt 497 = data_497 := by
  rw [rowAt, dif_neg (by decide : ¬ 497 < 6), entry_497_checked]
  change forkRow [placeRow ⟨36, 2, 3, 4⟩ (rowAt 36), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨410, 0, 7, 3⟩ (rowAt 410)] = data_497
  rw [row_36, row_167, row_410]
  apply row_ext <;> decide +kernel
theorem entry_good_497 : EntryGood 497 := by
  unfold EntryGood
  rw [entry_497_checked]
  decide +kernel
theorem good_497 : Good (rowAt 497) := by
  rw [row_497]
  unfold Good
  decide +kernel

theorem entry_498_checked : entryAt 498 = entry_498 := by
  rw [entry_chunk_24 12 (by decide)]
  decide +kernel
theorem row_498 : rowAt 498 = data_498 := by
  rw [rowAt, dif_neg (by decide : ¬ 498 < 6), entry_498_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨298, 2, 2, 4⟩ (rowAt 298)] = data_498
  rw [row_14, row_298]
  apply row_ext <;> decide +kernel
theorem entry_good_498 : EntryGood 498 := by
  unfold EntryGood
  rw [entry_498_checked]
  decide +kernel
theorem good_498 : Good (rowAt 498) := by
  rw [row_498]
  unfold Good
  decide +kernel

theorem entry_499_checked : entryAt 499 = entry_499 := by
  rw [entry_chunk_24 13 (by decide)]
  decide +kernel
theorem row_499 : rowAt 499 = data_499 := by
  rw [rowAt, dif_neg (by decide : ¬ 499 < 6), entry_499_checked]
  change forkRow [placeRow ⟨493, 0, 5, 4⟩ (rowAt 493), placeRow ⟨25, 1, 4, 5⟩ (rowAt 25), placeRow ⟨478, 0, 2, 4⟩ (rowAt 478)] = data_499
  rw [row_493, row_25, row_478]
  apply row_ext <;> decide +kernel
theorem entry_good_499 : EntryGood 499 := by
  unfold EntryGood
  rw [entry_499_checked]
  decide +kernel
theorem good_499 : Good (rowAt 499) := by
  rw [row_499]
  unfold Good
  decide +kernel


theorem block15_group02_piece00_correct : (rowAt 496 = data_496 ∧ Good (rowAt 496) ∧ EntryGood 496) ∧ (rowAt 497 = data_497 ∧ Good (rowAt 497) ∧ EntryGood 497) ∧ (rowAt 498 = data_498 ∧ Good (rowAt 498) ∧ EntryGood 498) ∧ (rowAt 499 = data_499 ∧ Good (rowAt 499) ∧ EntryGood 499) ∧ True := by
  exact ⟨⟨row_496, good_496, entry_good_496⟩, ⟨row_497, good_497, entry_good_497⟩, ⟨row_498, good_498, entry_good_498⟩, ⟨row_499, good_499, entry_good_499⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
