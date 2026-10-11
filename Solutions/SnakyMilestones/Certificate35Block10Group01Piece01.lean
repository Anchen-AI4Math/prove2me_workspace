import Solutions.SnakyMilestones.Certificate35Block10Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_332_checked : entryAt 332 = entry_332 := by
  rw [entry_chunk_16 6 (by decide)]
  decide +kernel
theorem row_332 : rowAt 332 = data_332 := by
  rw [rowAt, dif_neg (by decide : ¬ 332 < 6), entry_332_checked]
  change forkRow [placeRow ⟨67, 4, 3, 4⟩ (rowAt 67), placeRow ⟨289, 2, 5, 1⟩ (rowAt 289)] = data_332
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_332 : EntryGood 332 := by
  unfold EntryGood
  rw [entry_332_checked]
  decide +kernel
theorem good_332 : Good (rowAt 332) := by
  rw [row_332]
  unfold Good
  decide +kernel

theorem entry_333_checked : entryAt 333 = entry_333 := by
  rw [entry_chunk_16 7 (by decide)]
  decide +kernel
theorem row_333 : rowAt 333 = data_333 := by
  rw [rowAt, dif_neg (by decide : ¬ 333 < 6), entry_333_checked]
  change forkRow [placeRow ⟨317, 0, 5, 4⟩ (rowAt 317), placeRow ⟨1, 5, 4, 3⟩ (rowAt 1)] = data_333
  rw [row_317, row_1]
  apply row_ext <;> decide +kernel
theorem entry_good_333 : EntryGood 333 := by
  unfold EntryGood
  rw [entry_333_checked]
  decide +kernel
theorem good_333 : Good (rowAt 333) := by
  rw [row_333]
  unfold Good
  decide +kernel

theorem entry_334_checked : entryAt 334 = entry_334 := by
  rw [entry_chunk_16 8 (by decide)]
  decide +kernel
theorem row_334 : rowAt 334 = data_334 := by
  rw [rowAt, dif_neg (by decide : ¬ 334 < 6), entry_334_checked]
  change forkRow [placeRow ⟨67, 6, 3, 2⟩ (rowAt 67), placeRow ⟨289, 0, 5, 5⟩ (rowAt 289)] = data_334
  rw [row_67, row_289]
  apply row_ext <;> decide +kernel
theorem entry_good_334 : EntryGood 334 := by
  unfold EntryGood
  rw [entry_334_checked]
  decide +kernel
theorem good_334 : Good (rowAt 334) := by
  rw [row_334]
  unfold Good
  decide +kernel

theorem entry_335_checked : entryAt 335 = entry_335 := by
  rw [entry_chunk_16 9 (by decide)]
  decide +kernel
theorem row_335 : rowAt 335 = data_335 := by
  rw [rowAt, dif_neg (by decide : ¬ 335 < 6), entry_335_checked]
  change forkRow [placeRow ⟨196, 3, 1, 3⟩ (rowAt 196), placeRow ⟨162, 1, 5, 4⟩ (rowAt 162)] = data_335
  rw [row_196, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_335 : EntryGood 335 := by
  unfold EntryGood
  rw [entry_335_checked]
  decide +kernel
theorem good_335 : Good (rowAt 335) := by
  rw [row_335]
  unfold Good
  decide +kernel

theorem block10_group01_piece01_correct : (rowAt 332 = data_332 ∧ Good (rowAt 332) ∧ EntryGood 332) ∧ (rowAt 333 = data_333 ∧ Good (rowAt 333) ∧ EntryGood 333) ∧ (rowAt 334 = data_334 ∧ Good (rowAt 334) ∧ EntryGood 334) ∧ (rowAt 335 = data_335 ∧ Good (rowAt 335) ∧ EntryGood 335) ∧ True := by
  exact ⟨⟨row_332, good_332, entry_good_332⟩, ⟨row_333, good_333, entry_good_333⟩, ⟨row_334, good_334, entry_good_334⟩, ⟨row_335, good_335, entry_good_335⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
