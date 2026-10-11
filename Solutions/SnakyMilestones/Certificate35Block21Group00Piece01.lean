import Solutions.SnakyMilestones.Certificate35Block21Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_614_checked : entryAt 614 = entry_614 := by
  rw [entry_chunk_30 8 (by decide)]
  decide +kernel
theorem row_614 : rowAt 614 = data_614 := by
  rw [rowAt, dif_neg (by decide : ¬ 614 < 6), entry_614_checked]
  change forkRow [placeRow ⟨608, 1, 7, 5⟩ (rowAt 608), placeRow ⟨543, 3, 5, 6⟩ (rowAt 543), placeRow ⟨370, 6, 3, 4⟩ (rowAt 370), placeRow ⟨392, 7, 3, 4⟩ (rowAt 392), placeRow ⟨610, 3, 5, 6⟩ (rowAt 610), placeRow ⟨600, 0, 6, 4⟩ (rowAt 600), placeRow ⟨613, 0, 6, 4⟩ (rowAt 613)] = data_614
  rw [row_608, row_543, row_370, row_392, row_610, row_600, row_613]
  apply row_ext <;> decide +kernel
theorem entry_good_614 : EntryGood 614 := by
  unfold EntryGood
  rw [entry_614_checked]
  decide +kernel
theorem good_614 : Good (rowAt 614) := by
  rw [row_614]
  unfold Good
  decide +kernel

theorem block21_group00_piece01_correct : (rowAt 614 = data_614 ∧ Good (rowAt 614) ∧ EntryGood 614) ∧ True := by
  exact ⟨⟨row_614, good_614, entry_good_614⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
