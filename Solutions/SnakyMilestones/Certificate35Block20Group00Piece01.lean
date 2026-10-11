import Solutions.SnakyMilestones.Certificate35Block20Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_605_checked : entryAt 605 = entry_605 := by
  rw [entry_chunk_29 19 (by decide)]
  decide +kernel
theorem row_605 : rowAt 605 = data_605 := by
  rw [rowAt, dif_neg (by decide : ¬ 605 < 6), entry_605_checked]
  change forkRow [placeRow ⟨400, 5, 4, 3⟩ (rowAt 400), placeRow ⟨383, 6, 3, 4⟩ (rowAt 383), placeRow ⟨530, 4, 4, 3⟩ (rowAt 530), placeRow ⟨596, 1, 3, 4⟩ (rowAt 596), placeRow ⟨522, 2, 4, 3⟩ (rowAt 522), placeRow ⟨598, 0, 4, 3⟩ (rowAt 598), placeRow ⟨537, 3, 3, 4⟩ (rowAt 537), placeRow ⟨520, 1, 4, 3⟩ (rowAt 520), placeRow ⟨550, 4, 4, 3⟩ (rowAt 550)] = data_605
  rw [row_400, row_383, row_530, row_596, row_522, row_598, row_537, row_520, row_550]
  apply row_ext <;> decide +kernel
theorem entry_good_605 : EntryGood 605 := by
  unfold EntryGood
  rw [entry_605_checked]
  decide +kernel
theorem good_605 : Good (rowAt 605) := by
  rw [row_605]
  unfold Good
  decide +kernel

theorem entry_606_checked : entryAt 606 = entry_606 := by
  rw [entry_chunk_30 0 (by decide)]
  decide +kernel
theorem row_606 : rowAt 606 = data_606 := by
  rw [rowAt, dif_neg (by decide : ¬ 606 < 6), entry_606_checked]
  change forkRow [placeRow ⟨123, 1, 4, 3⟩ (rowAt 123), placeRow ⟨274, 0, 4, 3⟩ (rowAt 274), placeRow ⟨605, 0, 6, 4⟩ (rowAt 605), placeRow ⟨119, 1, 4, 3⟩ (rowAt 119)] = data_606
  rw [row_123, row_274, row_605, row_119]
  apply row_ext <;> decide +kernel
theorem entry_good_606 : EntryGood 606 := by
  unfold EntryGood
  rw [entry_606_checked]
  decide +kernel
theorem good_606 : Good (rowAt 606) := by
  rw [row_606]
  unfold Good
  decide +kernel

theorem entry_607_checked : entryAt 607 = entry_607 := by
  rw [entry_chunk_30 1 (by decide)]
  decide +kernel
theorem row_607 : rowAt 607 = data_607 := by
  rw [rowAt, dif_neg (by decide : ¬ 607 < 6), entry_607_checked]
  change forkRow [placeRow ⟨420, 3, 1, 2⟩ (rowAt 420), placeRow ⟨419, 3, 1, 4⟩ (rowAt 419), placeRow ⟨589, 0, 5, 5⟩ (rowAt 589), placeRow ⟨314, 0, 3, 4⟩ (rowAt 314), placeRow ⟨571, 1, 7, 3⟩ (rowAt 571)] = data_607
  rw [row_420, row_419, row_589, row_314, row_571]
  apply row_ext <;> decide +kernel
theorem entry_good_607 : EntryGood 607 := by
  unfold EntryGood
  rw [entry_607_checked]
  decide +kernel
theorem good_607 : Good (rowAt 607) := by
  rw [row_607]
  unfold Good
  decide +kernel

theorem entry_608_checked : entryAt 608 = entry_608 := by
  rw [entry_chunk_30 2 (by decide)]
  decide +kernel
theorem row_608 : rowAt 608 = data_608 := by
  rw [rowAt, dif_neg (by decide : ¬ 608 < 6), entry_608_checked]
  change forkRow [placeRow ⟨486, 4, 4, 5⟩ (rowAt 486), placeRow ⟨515, 1, 4, 5⟩ (rowAt 515), placeRow ⟨580, 0, 4, 5⟩ (rowAt 580), placeRow ⟨521, 0, 4, 5⟩ (rowAt 521), placeRow ⟨581, 4, 4, 5⟩ (rowAt 581), placeRow ⟨593, 0, 4, 5⟩ (rowAt 593), placeRow ⟨599, 4, 4, 5⟩ (rowAt 599), placeRow ⟨606, 1, 6, 2⟩ (rowAt 606)] = data_608
  rw [row_486, row_515, row_580, row_521, row_581, row_593, row_599, row_606]
  apply row_ext <;> decide +kernel
theorem entry_good_608 : EntryGood 608 := by
  unfold EntryGood
  rw [entry_608_checked]
  decide +kernel
theorem good_608 : Good (rowAt 608) := by
  rw [row_608]
  unfold Good
  decide +kernel

theorem block20_group00_piece01_correct : (rowAt 605 = data_605 ∧ Good (rowAt 605) ∧ EntryGood 605) ∧ (rowAt 606 = data_606 ∧ Good (rowAt 606) ∧ EntryGood 606) ∧ (rowAt 607 = data_607 ∧ Good (rowAt 607) ∧ EntryGood 607) ∧ (rowAt 608 = data_608 ∧ Good (rowAt 608) ∧ EntryGood 608) ∧ True := by
  exact ⟨⟨row_605, good_605, entry_good_605⟩, ⟨row_606, good_606, entry_good_606⟩, ⟨row_607, good_607, entry_good_607⟩, ⟨row_608, good_608, entry_good_608⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
