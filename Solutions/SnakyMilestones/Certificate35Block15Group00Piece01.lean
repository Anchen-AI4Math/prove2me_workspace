import Solutions.SnakyMilestones.Certificate35Block15Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_484_checked : entryAt 484 = entry_484 := by
  rw [entry_chunk_23 18 (by decide)]
  decide +kernel
theorem row_484 : rowAt 484 = data_484 := by
  rw [rowAt, dif_neg (by decide : ¬ 484 < 6), entry_484_checked]
  change forkRow [placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨349, 3, 1, 5⟩ (rowAt 349), placeRow ⟨163, 2, 5, 4⟩ (rowAt 163)] = data_484
  rw [row_25, row_107, row_349, row_163]
  apply row_ext <;> decide +kernel
theorem entry_good_484 : EntryGood 484 := by
  unfold EntryGood
  rw [entry_484_checked]
  decide +kernel
theorem good_484 : Good (rowAt 484) := by
  rw [row_484]
  unfold Good
  decide +kernel

theorem entry_485_checked : entryAt 485 = entry_485 := by
  rw [entry_chunk_23 19 (by decide)]
  decide +kernel
theorem row_485 : rowAt 485 = data_485 := by
  rw [rowAt, dif_neg (by decide : ¬ 485 < 6), entry_485_checked]
  change forkRow [placeRow ⟨484, 0, 5, 4⟩ (rowAt 484), placeRow ⟨2, 3, 4, 3⟩ (rowAt 2)] = data_485
  rw [row_484, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_485 : EntryGood 485 := by
  unfold EntryGood
  rw [entry_485_checked]
  decide +kernel
theorem good_485 : Good (rowAt 485) := by
  rw [row_485]
  unfold Good
  decide +kernel

theorem entry_486_checked : entryAt 486 = entry_486 := by
  rw [entry_chunk_24 0 (by decide)]
  decide +kernel
theorem row_486 : rowAt 486 = data_486 := by
  rw [rowAt, dif_neg (by decide : ¬ 486 < 6), entry_486_checked]
  change forkRow [placeRow ⟨2, 5, 4, 2⟩ (rowAt 2), placeRow ⟨485, 0, 5, 3⟩ (rowAt 485)] = data_486
  rw [row_2, row_485]
  apply row_ext <;> decide +kernel
theorem entry_good_486 : EntryGood 486 := by
  unfold EntryGood
  rw [entry_486_checked]
  decide +kernel
theorem good_486 : Good (rowAt 486) := by
  rw [row_486]
  unfold Good
  decide +kernel

theorem entry_487_checked : entryAt 487 = entry_487 := by
  rw [entry_chunk_24 1 (by decide)]
  decide +kernel
theorem row_487 : rowAt 487 = data_487 := by
  rw [rowAt, dif_neg (by decide : ¬ 487 < 6), entry_487_checked]
  change forkRow [placeRow ⟨2, 3, 4, 3⟩ (rowAt 2), placeRow ⟨481, 0, 5, 4⟩ (rowAt 481)] = data_487
  rw [row_2, row_481]
  apply row_ext <;> decide +kernel
theorem entry_good_487 : EntryGood 487 := by
  unfold EntryGood
  rw [entry_487_checked]
  decide +kernel
theorem good_487 : Good (rowAt 487) := by
  rw [row_487]
  unfold Good
  decide +kernel

theorem block15_group00_piece01_correct : (rowAt 484 = data_484 ∧ Good (rowAt 484) ∧ EntryGood 484) ∧ (rowAt 485 = data_485 ∧ Good (rowAt 485) ∧ EntryGood 485) ∧ (rowAt 486 = data_486 ∧ Good (rowAt 486) ∧ EntryGood 486) ∧ (rowAt 487 = data_487 ∧ Good (rowAt 487) ∧ EntryGood 487) ∧ True := by
  exact ⟨⟨row_484, good_484, entry_good_484⟩, ⟨row_485, good_485, entry_good_485⟩, ⟨row_486, good_486, entry_good_486⟩, ⟨row_487, good_487, entry_good_487⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
