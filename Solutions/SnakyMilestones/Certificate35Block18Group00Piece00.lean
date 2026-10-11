import Definitions.Def_Snaky35Cache18
import Solutions.SnakyMilestones.Certificate35Part17
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_571_checked : entryAt 571 = entry_571 := by
  rw [entry_chunk_28 5 (by decide)]
  decide +kernel
theorem row_571 : rowAt 571 = data_571 := by
  rw [rowAt, dif_neg (by decide : ¬ 571 < 6), entry_571_checked]
  change forkRow [placeRow ⟨293, 0, 4, 3⟩ (rowAt 293), placeRow ⟨570, 0, 4, 3⟩ (rowAt 570), placeRow ⟨382, 0, 4, 3⟩ (rowAt 382), placeRow ⟨556, 4, 2, 4⟩ (rowAt 556)] = data_571
  rw [row_293, row_570, row_382, row_556]
  apply row_ext <;> decide +kernel
theorem entry_good_571 : EntryGood 571 := by
  unfold EntryGood
  rw [entry_571_checked]
  decide +kernel
theorem good_571 : Good (rowAt 571) := by
  rw [row_571]
  unfold Good
  decide +kernel

theorem entry_572_checked : entryAt 572 = entry_572 := by
  rw [entry_chunk_28 6 (by decide)]
  decide +kernel
theorem row_572 : rowAt 572 = data_572 := by
  rw [rowAt, dif_neg (by decide : ¬ 572 < 6), entry_572_checked]
  change forkRow [placeRow ⟨564, 1, 6, 6⟩ (rowAt 564), placeRow ⟨465, 3, 3, 4⟩ (rowAt 465), placeRow ⟨385, 4, 3, 4⟩ (rowAt 385), placeRow ⟨364, 7, 3, 4⟩ (rowAt 364), placeRow ⟨499, 1, 6, 5⟩ (rowAt 499)] = data_572
  rw [row_564, row_465, row_385, row_364, row_499]
  apply row_ext <;> decide +kernel
theorem entry_good_572 : EntryGood 572 := by
  unfold EntryGood
  rw [entry_572_checked]
  decide +kernel
theorem good_572 : Good (rowAt 572) := by
  rw [row_572]
  unfold Good
  decide +kernel

theorem entry_573_checked : entryAt 573 = entry_573 := by
  rw [entry_chunk_28 7 (by decide)]
  decide +kernel
theorem row_573 : rowAt 573 = data_573 := by
  rw [rowAt, dif_neg (by decide : ¬ 573 < 6), entry_573_checked]
  change forkRow [placeRow ⟨527, 2, 3, 1⟩ (rowAt 527), placeRow ⟨499, 4, 3, 4⟩ (rowAt 499), placeRow ⟨527, 6, 5, 1⟩ (rowAt 527), placeRow ⟨499, 0, 5, 4⟩ (rowAt 499), placeRow ⟨407, 4, 4, 1⟩ (rowAt 407), placeRow ⟨531, 7, 2, 4⟩ (rowAt 531), placeRow ⟨407, 0, 4, 1⟩ (rowAt 407)] = data_573
  rw [row_527, row_499, row_407, row_531]
  apply row_ext <;> decide +kernel
theorem entry_good_573 : EntryGood 573 := by
  unfold EntryGood
  rw [entry_573_checked]
  decide +kernel
theorem good_573 : Good (rowAt 573) := by
  rw [row_573]
  unfold Good
  decide +kernel

theorem entry_574_checked : entryAt 574 = entry_574 := by
  rw [entry_chunk_28 8 (by decide)]
  decide +kernel
theorem row_574 : rowAt 574 = data_574 := by
  rw [rowAt, dif_neg (by decide : ¬ 574 < 6), entry_574_checked]
  change forkRow [placeRow ⟨497, 0, 2, 4⟩ (rowAt 497), placeRow ⟨539, 4, 4, 6⟩ (rowAt 539), placeRow ⟨355, 0, 2, 4⟩ (rowAt 355), placeRow ⟨390, 3, 2, 4⟩ (rowAt 390), placeRow ⟨544, 0, 2, 4⟩ (rowAt 544), placeRow ⟨462, 1, 4, 5⟩ (rowAt 462), placeRow ⟨563, 4, 5, 4⟩ (rowAt 563), placeRow ⟨540, 4, 4, 6⟩ (rowAt 540), placeRow ⟨518, 0, 2, 4⟩ (rowAt 518), placeRow ⟨495, 4, 2, 4⟩ (rowAt 495)] = data_574
  rw [row_497, row_539, row_355, row_390, row_544, row_462, row_563, row_540, row_518, row_495]
  apply row_ext <;> decide +kernel
theorem entry_good_574 : EntryGood 574 := by
  unfold EntryGood
  rw [entry_574_checked]
  decide +kernel
theorem good_574 : Good (rowAt 574) := by
  rw [row_574]
  unfold Good
  decide +kernel


theorem block18_group00_piece00_correct : (rowAt 571 = data_571 ∧ Good (rowAt 571) ∧ EntryGood 571) ∧ (rowAt 572 = data_572 ∧ Good (rowAt 572) ∧ EntryGood 572) ∧ (rowAt 573 = data_573 ∧ Good (rowAt 573) ∧ EntryGood 573) ∧ (rowAt 574 = data_574 ∧ Good (rowAt 574) ∧ EntryGood 574) ∧ True := by
  exact ⟨⟨row_571, good_571, entry_good_571⟩, ⟨row_572, good_572, entry_good_572⟩, ⟨row_573, good_573, entry_good_573⟩, ⟨row_574, good_574, entry_good_574⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
