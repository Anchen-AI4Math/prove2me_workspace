import Solutions.SnakyMilestones.Certificate35Block16Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_532_checked : entryAt 532 = entry_532 := by
  rw [entry_chunk_26 6 (by decide)]
  decide +kernel
theorem row_532 : rowAt 532 = data_532 := by
  rw [rowAt, dif_neg (by decide : ¬ 532 < 6), entry_532_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨6, 7, 3, 0⟩ (rowAt 6)] = data_532
  rw [row_504, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_532 : EntryGood 532 := by
  unfold EntryGood
  rw [entry_532_checked]
  decide +kernel
theorem good_532 : Good (rowAt 532) := by
  rw [row_532]
  unfold Good
  decide +kernel

theorem entry_533_checked : entryAt 533 = entry_533 := by
  rw [entry_chunk_26 7 (by decide)]
  decide +kernel
theorem row_533 : rowAt 533 = data_533 := by
  rw [rowAt, dif_neg (by decide : ¬ 533 < 6), entry_533_checked]
  change forkRow [placeRow ⟨318, 4, 4, 5⟩ (rowAt 318), placeRow ⟨319, 7, 5, 1⟩ (rowAt 319), placeRow ⟨407, 4, 4, 1⟩ (rowAt 407), placeRow ⟨173, 3, 4, 5⟩ (rowAt 173), placeRow ⟨217, 1, 4, 5⟩ (rowAt 217)] = data_533
  rw [row_318, row_319, row_407, row_173, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_533 : EntryGood 533 := by
  unfold EntryGood
  rw [entry_533_checked]
  decide +kernel
theorem good_533 : Good (rowAt 533) := by
  rw [row_533]
  unfold Good
  decide +kernel

theorem entry_534_checked : entryAt 534 = entry_534 := by
  rw [entry_chunk_26 8 (by decide)]
  decide +kernel
theorem row_534 : rowAt 534 = data_534 := by
  rw [rowAt, dif_neg (by decide : ¬ 534 < 6), entry_534_checked]
  change forkRow [placeRow ⟨434, 0, 4, 6⟩ (rowAt 434), placeRow ⟨12, 6, 1, 3⟩ (rowAt 12)] = data_534
  rw [row_434, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_534 : EntryGood 534 := by
  unfold EntryGood
  rw [entry_534_checked]
  decide +kernel
theorem good_534 : Good (rowAt 534) := by
  rw [row_534]
  unfold Good
  decide +kernel

theorem entry_535_checked : entryAt 535 = entry_535 := by
  rw [entry_chunk_26 9 (by decide)]
  decide +kernel
theorem row_535 : rowAt 535 = data_535 := by
  rw [rowAt, dif_neg (by decide : ¬ 535 < 6), entry_535_checked]
  change forkRow [placeRow ⟨444, 0, 4, 5⟩ (rowAt 444), placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_535
  rw [row_444, row_426, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_535 : EntryGood 535 := by
  unfold EntryGood
  rw [entry_535_checked]
  decide +kernel
theorem good_535 : Good (rowAt 535) := by
  rw [row_535]
  unfold Good
  decide +kernel

theorem block16_group02_piece01_correct : (rowAt 532 = data_532 ∧ Good (rowAt 532) ∧ EntryGood 532) ∧ (rowAt 533 = data_533 ∧ Good (rowAt 533) ∧ EntryGood 533) ∧ (rowAt 534 = data_534 ∧ Good (rowAt 534) ∧ EntryGood 534) ∧ (rowAt 535 = data_535 ∧ Good (rowAt 535) ∧ EntryGood 535) ∧ True := by
  exact ⟨⟨row_532, good_532, entry_good_532⟩, ⟨row_533, good_533, entry_good_533⟩, ⟨row_534, good_534, entry_good_534⟩, ⟨row_535, good_535, entry_good_535⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
