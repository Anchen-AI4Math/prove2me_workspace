import Definitions.Def_Snaky35Cache21
import Solutions.SnakyMilestones.Certificate35Part20
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_610_checked : entryAt 610 = entry_610 := by
  rw [entry_chunk_30 4 (by decide)]
  decide +kernel
theorem row_610 : rowAt 610 = data_610 := by
  rw [rowAt, dif_neg (by decide : ¬ 610 < 6), entry_610_checked]
  change forkRow [placeRow ⟨221, 2, 5, 4⟩ (rowAt 221), placeRow ⟨286, 5, 5, 4⟩ (rowAt 286), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨472, 1, 5, 4⟩ (rowAt 472), placeRow ⟨566, 1, 5, 4⟩ (rowAt 566), placeRow ⟨532, 5, 5, 4⟩ (rowAt 532), placeRow ⟨542, 1, 5, 4⟩ (rowAt 542), placeRow ⟨609, 0, 2, 6⟩ (rowAt 609)] = data_610
  rw [row_221, row_286, row_107, row_472, row_566, row_532, row_542, row_609]
  apply row_ext <;> decide +kernel
theorem entry_good_610 : EntryGood 610 := by
  unfold EntryGood
  rw [entry_610_checked]
  decide +kernel
theorem good_610 : Good (rowAt 610) := by
  rw [row_610]
  unfold Good
  decide +kernel

theorem entry_611_checked : entryAt 611 = entry_611 := by
  rw [entry_chunk_30 5 (by decide)]
  decide +kernel
theorem row_611 : rowAt 611 = data_611 := by
  rw [rowAt, dif_neg (by decide : ¬ 611 < 6), entry_611_checked]
  change forkRow [placeRow ⟨456, 2, 5, 4⟩ (rowAt 456), placeRow ⟨456, 4, 1, 4⟩ (rowAt 456), placeRow ⟨594, 7, 1, 3⟩ (rowAt 594), placeRow ⟨594, 1, 5, 5⟩ (rowAt 594)] = data_611
  rw [row_456, row_594]
  apply row_ext <;> decide +kernel
theorem entry_good_611 : EntryGood 611 := by
  unfold EntryGood
  rw [entry_611_checked]
  decide +kernel
theorem good_611 : Good (rowAt 611) := by
  rw [row_611]
  unfold Good
  decide +kernel

theorem entry_612_checked : entryAt 612 = entry_612 := by
  rw [entry_chunk_30 6 (by decide)]
  decide +kernel
theorem row_612 : rowAt 612 = data_612 := by
  rw [rowAt, dif_neg (by decide : ¬ 612 < 6), entry_612_checked]
  change forkRow [placeRow ⟨589, 1, 5, 5⟩ (rowAt 589), placeRow ⟨589, 7, 0, 3⟩ (rowAt 589)] = data_612
  rw [row_589]
  apply row_ext <;> decide +kernel
theorem entry_good_612 : EntryGood 612 := by
  unfold EntryGood
  rw [entry_612_checked]
  decide +kernel
theorem good_612 : Good (rowAt 612) := by
  rw [row_612]
  unfold Good
  decide +kernel

theorem entry_613_checked : entryAt 613 = entry_613 := by
  rw [entry_chunk_30 7 (by decide)]
  decide +kernel
theorem row_613 : rowAt 613 = data_613 := by
  rw [rowAt, dif_neg (by decide : ¬ 613 < 6), entry_613_checked]
  change forkRow [placeRow ⟨607, 5, 5, 4⟩ (rowAt 607), placeRow ⟨503, 3, 1, 4⟩ (rowAt 503), placeRow ⟨592, 7, 1, 3⟩ (rowAt 592), placeRow ⟨592, 5, 5, 3⟩ (rowAt 592), placeRow ⟨607, 7, 1, 4⟩ (rowAt 607), placeRow ⟨612, 4, 1, 4⟩ (rowAt 612), placeRow ⟨612, 0, 5, 4⟩ (rowAt 612)] = data_613
  rw [row_607, row_503, row_592, row_612]
  apply row_ext <;> decide +kernel
theorem entry_good_613 : EntryGood 613 := by
  unfold EntryGood
  rw [entry_613_checked]
  decide +kernel
theorem good_613 : Good (rowAt 613) := by
  rw [row_613]
  unfold Good
  decide +kernel


theorem block21_group00_piece00_correct : (rowAt 610 = data_610 ∧ Good (rowAt 610) ∧ EntryGood 610) ∧ (rowAt 611 = data_611 ∧ Good (rowAt 611) ∧ EntryGood 611) ∧ (rowAt 612 = data_612 ∧ Good (rowAt 612) ∧ EntryGood 612) ∧ (rowAt 613 = data_613 ∧ Good (rowAt 613) ∧ EntryGood 613) ∧ True := by
  exact ⟨⟨row_610, good_610, entry_good_610⟩, ⟨row_611, good_611, entry_good_611⟩, ⟨row_612, good_612, entry_good_612⟩, ⟨row_613, good_613, entry_good_613⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
