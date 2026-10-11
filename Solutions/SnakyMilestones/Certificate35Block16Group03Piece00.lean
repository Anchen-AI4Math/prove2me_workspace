import Definitions.Def_Snaky35Cache16
import Solutions.SnakyMilestones.Certificate35Block16Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_536_checked : entryAt 536 = entry_536 := by
  rw [entry_chunk_26 10 (by decide)]
  decide +kernel
theorem row_536 : rowAt 536 = data_536 := by
  rw [rowAt, dif_neg (by decide : ¬ 536 < 6), entry_536_checked]
  change forkRow [placeRow ⟨307, 0, 4, 3⟩ (rowAt 307), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨534, 0, 5, 2⟩ (rowAt 534)] = data_536
  rw [row_307, row_244, row_26, row_534]
  apply row_ext <;> decide +kernel
theorem entry_good_536 : EntryGood 536 := by
  unfold EntryGood
  rw [entry_536_checked]
  decide +kernel
theorem good_536 : Good (rowAt 536) := by
  rw [row_536]
  unfold Good
  decide +kernel

theorem entry_537_checked : entryAt 537 = entry_537 := by
  rw [entry_chunk_26 11 (by decide)]
  decide +kernel
theorem row_537 : rowAt 537 = data_537 := by
  rw [rowAt, dif_neg (by decide : ¬ 537 < 6), entry_537_checked]
  change forkRow [placeRow ⟨373, 2, 2, 4⟩ (rowAt 373), placeRow ⟨271, 3, 3, 3⟩ (rowAt 271), placeRow ⟨176, 1, 4, 6⟩ (rowAt 176), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330)] = data_537
  rw [row_373, row_271, row_176, row_330]
  apply row_ext <;> decide +kernel
theorem entry_good_537 : EntryGood 537 := by
  unfold EntryGood
  rw [entry_537_checked]
  decide +kernel
theorem good_537 : Good (rowAt 537) := by
  rw [row_537]
  unfold Good
  decide +kernel

theorem entry_538_checked : entryAt 538 = entry_538 := by
  rw [entry_chunk_26 12 (by decide)]
  decide +kernel
theorem row_538 : rowAt 538 = data_538 := by
  rw [rowAt, dif_neg (by decide : ¬ 538 < 6), entry_538_checked]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨470, 0, 4, 5⟩ (rowAt 470), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64), placeRow ⟨55, 4, 3, 4⟩ (rowAt 55)] = data_538
  rw [row_63, row_470, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_538 : EntryGood 538 := by
  unfold EntryGood
  rw [entry_538_checked]
  decide +kernel
theorem good_538 : Good (rowAt 538) := by
  rw [row_538]
  unfold Good
  decide +kernel

theorem entry_539_checked : entryAt 539 = entry_539 := by
  rw [entry_chunk_26 13 (by decide)]
  decide +kernel
theorem row_539 : rowAt 539 = data_539 := by
  rw [rowAt, dif_neg (by decide : ¬ 539 < 6), entry_539_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨488, 3, 4, 3⟩ (rowAt 488), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨516, 0, 5, 4⟩ (rowAt 516)] = data_539
  rw [row_51, row_488, row_428, row_516]
  apply row_ext <;> decide +kernel
theorem entry_good_539 : EntryGood 539 := by
  unfold EntryGood
  rw [entry_539_checked]
  decide +kernel
theorem good_539 : Good (rowAt 539) := by
  rw [row_539]
  unfold Good
  decide +kernel


theorem block16_group03_piece00_correct : (rowAt 536 = data_536 ∧ Good (rowAt 536) ∧ EntryGood 536) ∧ (rowAt 537 = data_537 ∧ Good (rowAt 537) ∧ EntryGood 537) ∧ (rowAt 538 = data_538 ∧ Good (rowAt 538) ∧ EntryGood 538) ∧ (rowAt 539 = data_539 ∧ Good (rowAt 539) ∧ EntryGood 539) ∧ True := by
  exact ⟨⟨row_536, good_536, entry_good_536⟩, ⟨row_537, good_537, entry_good_537⟩, ⟨row_538, good_538, entry_good_538⟩, ⟨row_539, good_539, entry_good_539⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
