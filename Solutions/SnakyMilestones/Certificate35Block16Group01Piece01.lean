import Solutions.SnakyMilestones.Certificate35Block16Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_524_checked : entryAt 524 = entry_524 := by
  rw [entry_chunk_25 18 (by decide)]
  decide +kernel
theorem row_524 : rowAt 524 = data_524 := by
  rw [rowAt, dif_neg (by decide : ¬ 524 < 6), entry_524_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_524
  rw [row_504, row_180, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_524 : EntryGood 524 := by
  unfold EntryGood
  rw [entry_524_checked]
  decide +kernel
theorem good_524 : Good (rowAt 524) := by
  rw [row_524]
  unfold Good
  decide +kernel

theorem entry_525_checked : entryAt 525 = entry_525 := by
  rw [entry_chunk_25 19 (by decide)]
  decide +kernel
theorem row_525 : rowAt 525 = data_525 := by
  rw [rowAt, dif_neg (by decide : ¬ 525 < 6), entry_525_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨430, 0, 4, 6⟩ (rowAt 430), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107)] = data_525
  rw [row_303, row_25, row_430, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_525 : EntryGood 525 := by
  unfold EntryGood
  rw [entry_525_checked]
  decide +kernel
theorem good_525 : Good (rowAt 525) := by
  rw [row_525]
  unfold Good
  decide +kernel

theorem entry_526_checked : entryAt 526 = entry_526 := by
  rw [entry_chunk_26 0 (by decide)]
  decide +kernel
theorem row_526 : rowAt 526 = data_526 := by
  rw [rowAt, dif_neg (by decide : ¬ 526 < 6), entry_526_checked]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (rowAt 359), placeRow ⟨416, 4, 2, 4⟩ (rowAt 416), placeRow ⟨327, 5, 4, 3⟩ (rowAt 327), placeRow ⟨489, 0, 5, 4⟩ (rowAt 489), placeRow ⟨399, 3, 2, 4⟩ (rowAt 399)] = data_526
  rw [row_359, row_416, row_327, row_489, row_399]
  apply row_ext <;> decide +kernel
theorem entry_good_526 : EntryGood 526 := by
  unfold EntryGood
  rw [entry_526_checked]
  decide +kernel
theorem good_526 : Good (rowAt 526) := by
  rw [row_526]
  unfold Good
  decide +kernel

theorem entry_527_checked : entryAt 527 = entry_527 := by
  rw [entry_chunk_26 1 (by decide)]
  decide +kernel
theorem row_527 : rowAt 527 = data_527 := by
  rw [rowAt, dif_neg (by decide : ¬ 527 < 6), entry_527_checked]
  change forkRow [placeRow ⟨387, 4, 4, 3⟩ (rowAt 387), placeRow ⟨38, 3, 4, 5⟩ (rowAt 38), placeRow ⟨491, 0, 5, 4⟩ (rowAt 491), placeRow ⟨519, 0, 6, 4⟩ (rowAt 519)] = data_527
  rw [row_387, row_38, row_491, row_519]
  apply row_ext <;> decide +kernel
theorem entry_good_527 : EntryGood 527 := by
  unfold EntryGood
  rw [entry_527_checked]
  decide +kernel
theorem good_527 : Good (rowAt 527) := by
  rw [row_527]
  unfold Good
  decide +kernel

theorem block16_group01_piece01_correct : (rowAt 524 = data_524 ∧ Good (rowAt 524) ∧ EntryGood 524) ∧ (rowAt 525 = data_525 ∧ Good (rowAt 525) ∧ EntryGood 525) ∧ (rowAt 526 = data_526 ∧ Good (rowAt 526) ∧ EntryGood 526) ∧ (rowAt 527 = data_527 ∧ Good (rowAt 527) ∧ EntryGood 527) ∧ True := by
  exact ⟨⟨row_524, good_524, entry_good_524⟩, ⟨row_525, good_525, entry_good_525⟩, ⟨row_526, good_526, entry_good_526⟩, ⟨row_527, good_527, entry_good_527⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
