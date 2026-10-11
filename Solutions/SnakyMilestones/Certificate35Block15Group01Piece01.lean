import Solutions.SnakyMilestones.Certificate35Block15Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_492_checked : entryAt 492 = entry_492 := by
  rw [entry_chunk_24 6 (by decide)]
  decide +kernel
theorem row_492 : rowAt 492 = data_492 := by
  rw [rowAt, dif_neg (by decide : ¬ 492 < 6), entry_492_checked]
  change forkRow [placeRow ⟨62, 4, 3, 4⟩ (rowAt 62), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨487, 0, 6, 6⟩ (rowAt 487)] = data_492
  rw [row_62, row_107, row_487]
  apply row_ext <;> decide +kernel
theorem entry_good_492 : EntryGood 492 := by
  unfold EntryGood
  rw [entry_492_checked]
  decide +kernel
theorem good_492 : Good (rowAt 492) := by
  rw [row_492]
  unfold Good
  decide +kernel

theorem entry_493_checked : entryAt 493 = entry_493 := by
  rw [entry_chunk_24 7 (by decide)]
  decide +kernel
theorem row_493 : rowAt 493 = data_493 := by
  rw [rowAt, dif_neg (by decide : ¬ 493 < 6), entry_493_checked]
  change forkRow [placeRow ⟨225, 0, 1, 4⟩ (rowAt 225), placeRow ⟨455, 0, 5, 3⟩ (rowAt 455), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨221, 0, 5, 4⟩ (rowAt 221)] = data_493
  rw [row_225, row_455, row_236, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_493 : EntryGood 493 := by
  unfold EntryGood
  rw [entry_493_checked]
  decide +kernel
theorem good_493 : Good (rowAt 493) := by
  rw [row_493]
  unfold Good
  decide +kernel

theorem entry_494_checked : entryAt 494 = entry_494 := by
  rw [entry_chunk_24 8 (by decide)]
  decide +kernel
theorem row_494 : rowAt 494 = data_494 := by
  rw [rowAt, dif_neg (by decide : ¬ 494 < 6), entry_494_checked]
  change forkRow [placeRow ⟨297, 4, 4, 5⟩ (rowAt 297), placeRow ⟨268, 4, 1, 5⟩ (rowAt 268), placeRow ⟨162, 5, 5, 4⟩ (rowAt 162)] = data_494
  rw [row_297, row_268, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_494 : EntryGood 494 := by
  unfold EntryGood
  rw [entry_494_checked]
  decide +kernel
theorem good_494 : Good (rowAt 494) := by
  rw [row_494]
  unfold Good
  decide +kernel

theorem entry_495_checked : entryAt 495 = entry_495 := by
  rw [entry_chunk_24 9 (by decide)]
  decide +kernel
theorem row_495 : rowAt 495 = data_495 := by
  rw [rowAt, dif_neg (by decide : ¬ 495 < 6), entry_495_checked]
  change forkRow [placeRow ⟨25, 6, 1, 3⟩ (rowAt 25), placeRow ⟨167, 4, 1, 4⟩ (rowAt 167), placeRow ⟨456, 4, 1, 4⟩ (rowAt 456)] = data_495
  rw [row_25, row_167, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_495 : EntryGood 495 := by
  unfold EntryGood
  rw [entry_495_checked]
  decide +kernel
theorem good_495 : Good (rowAt 495) := by
  rw [row_495]
  unfold Good
  decide +kernel

theorem block15_group01_piece01_correct : (rowAt 492 = data_492 ∧ Good (rowAt 492) ∧ EntryGood 492) ∧ (rowAt 493 = data_493 ∧ Good (rowAt 493) ∧ EntryGood 493) ∧ (rowAt 494 = data_494 ∧ Good (rowAt 494) ∧ EntryGood 494) ∧ (rowAt 495 = data_495 ∧ Good (rowAt 495) ∧ EntryGood 495) ∧ True := by
  exact ⟨⟨row_492, good_492, entry_good_492⟩, ⟨row_493, good_493, entry_good_493⟩, ⟨row_494, good_494, entry_good_494⟩, ⟨row_495, good_495, entry_good_495⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
