import Solutions.SnakyMilestones.Certificate35Block14Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_476_checked : entryAt 476 = entry_476 := by
  rw [entry_chunk_23 10 (by decide)]
  decide +kernel
theorem row_476 : rowAt 476 = data_476 := by
  rw [rowAt, dif_neg (by decide : ¬ 476 < 6), entry_476_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨473, 0, 5, 3⟩ (rowAt 473)] = data_476
  rw [row_0, row_473]
  apply row_ext <;> decide +kernel
theorem entry_good_476 : EntryGood 476 := by
  unfold EntryGood
  rw [entry_476_checked]
  decide +kernel
theorem good_476 : Good (rowAt 476) := by
  rw [row_476]
  unfold Good
  decide +kernel

theorem entry_477_checked : entryAt 477 = entry_477 := by
  rw [entry_chunk_23 11 (by decide)]
  decide +kernel
theorem row_477 : rowAt 477 = data_477 := by
  rw [rowAt, dif_neg (by decide : ¬ 477 < 6), entry_477_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨154, 7, 4, 5⟩ (rowAt 154), placeRow ⟨154, 3, 4, 0⟩ (rowAt 154), placeRow ⟨471, 2, 5, 4⟩ (rowAt 471)] = data_477
  rw [row_55, row_154, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_477 : EntryGood 477 := by
  unfold EntryGood
  rw [entry_477_checked]
  decide +kernel
theorem good_477 : Good (rowAt 477) := by
  rw [row_477]
  unfold Good
  decide +kernel

theorem entry_478_checked : entryAt 478 = entry_478 := by
  rw [entry_chunk_23 12 (by decide)]
  decide +kernel
theorem row_478 : rowAt 478 = data_478 := by
  rw [rowAt, dif_neg (by decide : ¬ 478 < 6), entry_478_checked]
  change forkRow [placeRow ⟨25, 3, 4, 5⟩ (rowAt 25), placeRow ⟨165, 2, 4, 5⟩ (rowAt 165), placeRow ⟨190, 0, 7, 4⟩ (rowAt 190)] = data_478
  rw [row_25, row_165, row_190]
  apply row_ext <;> decide +kernel
theorem entry_good_478 : EntryGood 478 := by
  unfold EntryGood
  rw [entry_478_checked]
  decide +kernel
theorem good_478 : Good (rowAt 478) := by
  rw [row_478]
  unfold Good
  decide +kernel

theorem entry_479_checked : entryAt 479 = entry_479 := by
  rw [entry_chunk_23 13 (by decide)]
  decide +kernel
theorem row_479 : rowAt 479 = data_479 := by
  rw [rowAt, dif_neg (by decide : ¬ 479 < 6), entry_479_checked]
  change forkRow [placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 0, 4, 5⟩ (rowAt 443), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443)] = data_479
  rw [row_55, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_479 : EntryGood 479 := by
  unfold EntryGood
  rw [entry_479_checked]
  decide +kernel
theorem good_479 : Good (rowAt 479) := by
  rw [row_479]
  unfold Good
  decide +kernel


theorem block14_group03_piece01_correct : (rowAt 476 = data_476 ∧ Good (rowAt 476) ∧ EntryGood 476) ∧ (rowAt 477 = data_477 ∧ Good (rowAt 477) ∧ EntryGood 477) ∧ (rowAt 478 = data_478 ∧ Good (rowAt 478) ∧ EntryGood 478) ∧ (rowAt 479 = data_479 ∧ Good (rowAt 479) ∧ EntryGood 479) ∧ True := by
  exact ⟨⟨row_476, good_476, entry_good_476⟩, ⟨row_477, good_477, entry_good_477⟩, ⟨row_478, good_478, entry_good_478⟩, ⟨row_479, good_479, entry_good_479⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
