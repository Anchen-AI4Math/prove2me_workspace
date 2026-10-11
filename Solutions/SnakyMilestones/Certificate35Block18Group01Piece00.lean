import Definitions.Def_Snaky35Cache18
import Solutions.SnakyMilestones.Certificate35Block18Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_579_checked : entryAt 579 = entry_579 := by
  rw [entry_chunk_28 13 (by decide)]
  decide +kernel
theorem row_579 : rowAt 579 = data_579 := by
  rw [rowAt, dif_neg (by decide : ¬ 579 < 6), entry_579_checked]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (rowAt 2), placeRow ⟨576, 4, 4, 5⟩ (rowAt 576)] = data_579
  rw [row_2, row_576]
  apply row_ext <;> decide +kernel
theorem entry_good_579 : EntryGood 579 := by
  unfold EntryGood
  rw [entry_579_checked]
  decide +kernel
theorem good_579 : Good (rowAt 579) := by
  rw [row_579]
  unfold Good
  decide +kernel

theorem entry_580_checked : entryAt 580 = entry_580 := by
  rw [entry_chunk_28 14 (by decide)]
  decide +kernel
theorem row_580 : rowAt 580 = data_580 := by
  rw [rowAt, dif_neg (by decide : ¬ 580 < 6), entry_580_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨579, 0, 3, 3⟩ (rowAt 579)] = data_580
  rw [row_2, row_579]
  apply row_ext <;> decide +kernel
theorem entry_good_580 : EntryGood 580 := by
  unfold EntryGood
  rw [entry_580_checked]
  decide +kernel
theorem good_580 : Good (rowAt 580) := by
  rw [row_580]
  unfold Good
  decide +kernel

theorem entry_581_checked : entryAt 581 = entry_581 := by
  rw [entry_chunk_28 15 (by decide)]
  decide +kernel
theorem row_581 : rowAt 581 = data_581 := by
  rw [rowAt, dif_neg (by decide : ¬ 581 < 6), entry_581_checked]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (rowAt 578), placeRow ⟨2, 5, 4, 2⟩ (rowAt 2)] = data_581
  rw [row_578, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_581 : EntryGood 581 := by
  unfold EntryGood
  rw [entry_581_checked]
  decide +kernel
theorem good_581 : Good (rowAt 581) := by
  rw [row_581]
  unfold Good
  decide +kernel

theorem entry_582_checked : entryAt 582 = entry_582 := by
  rw [entry_chunk_28 16 (by decide)]
  decide +kernel
theorem row_582 : rowAt 582 = data_582 := by
  rw [rowAt, dif_neg (by decide : ¬ 582 < 6), entry_582_checked]
  change forkRow [placeRow ⟨40, 3, 4, 3⟩ (rowAt 40), placeRow ⟨446, 5, 5, 3⟩ (rowAt 446), placeRow ⟨523, 0, 7, 0⟩ (rowAt 523), placeRow ⟨480, 4, 5, 3⟩ (rowAt 480), placeRow ⟨567, 4, 5, 4⟩ (rowAt 567)] = data_582
  rw [row_40, row_446, row_523, row_480, row_567]
  apply row_ext <;> decide +kernel
theorem entry_good_582 : EntryGood 582 := by
  unfold EntryGood
  rw [entry_582_checked]
  decide +kernel
theorem good_582 : Good (rowAt 582) := by
  rw [row_582]
  unfold Good
  decide +kernel


theorem block18_group01_piece00_correct : (rowAt 579 = data_579 ∧ Good (rowAt 579) ∧ EntryGood 579) ∧ (rowAt 580 = data_580 ∧ Good (rowAt 580) ∧ EntryGood 580) ∧ (rowAt 581 = data_581 ∧ Good (rowAt 581) ∧ EntryGood 581) ∧ (rowAt 582 = data_582 ∧ Good (rowAt 582) ∧ EntryGood 582) ∧ True := by
  exact ⟨⟨row_579, good_579, entry_good_579⟩, ⟨row_580, good_580, entry_good_580⟩, ⟨row_581, good_581, entry_good_581⟩, ⟨row_582, good_582, entry_good_582⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
