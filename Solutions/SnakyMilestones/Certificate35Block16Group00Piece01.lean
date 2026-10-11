import Solutions.SnakyMilestones.Certificate35Block16Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_516_checked : entryAt 516 = entry_516 := by
  rw [entry_chunk_25 10 (by decide)]
  decide +kernel
theorem row_516 : rowAt 516 = data_516 := by
  rw [rowAt, dif_neg (by decide : ¬ 516 < 6), entry_516_checked]
  change forkRow [placeRow ⟨329, 0, 4, 3⟩ (rowAt 329), placeRow ⟨244, 4, 2, 4⟩ (rowAt 244), placeRow ⟨10, 1, 4, 5⟩ (rowAt 10), placeRow ⟨506, 4, 2, 4⟩ (rowAt 506)] = data_516
  rw [row_329, row_244, row_10, row_506]
  apply row_ext <;> decide +kernel
theorem entry_good_516 : EntryGood 516 := by
  unfold EntryGood
  rw [entry_516_checked]
  decide +kernel
theorem good_516 : Good (rowAt 516) := by
  rw [row_516]
  unfold Good
  decide +kernel

theorem entry_517_checked : entryAt 517 = entry_517 := by
  rw [entry_chunk_25 11 (by decide)]
  decide +kernel
theorem row_517 : rowAt 517 = data_517 := by
  rw [rowAt, dif_neg (by decide : ¬ 517 < 6), entry_517_checked]
  change forkRow [placeRow ⟨496, 0, 2, 3⟩ (rowAt 496), placeRow ⟨140, 0, 4, 2⟩ (rowAt 140), placeRow ⟨193, 1, 4, 2⟩ (rowAt 193)] = data_517
  rw [row_496, row_140, row_193]
  apply row_ext <;> decide +kernel
theorem entry_good_517 : EntryGood 517 := by
  unfold EntryGood
  rw [entry_517_checked]
  decide +kernel
theorem good_517 : Good (rowAt 517) := by
  rw [row_517]
  unfold Good
  decide +kernel

theorem entry_518_checked : entryAt 518 = entry_518 := by
  rw [entry_chunk_25 12 (by decide)]
  decide +kernel
theorem row_518 : rowAt 518 = data_518 := by
  rw [rowAt, dif_neg (by decide : ¬ 518 < 6), entry_518_checked]
  change forkRow [placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514)] = data_518
  rw [row_9, row_514]
  apply row_ext <;> decide +kernel
theorem entry_good_518 : EntryGood 518 := by
  unfold EntryGood
  rw [entry_518_checked]
  decide +kernel
theorem good_518 : Good (rowAt 518) := by
  rw [row_518]
  unfold Good
  decide +kernel

theorem entry_519_checked : entryAt 519 = entry_519 := by
  rw [entry_chunk_25 13 (by decide)]
  decide +kernel
theorem row_519 : rowAt 519 = data_519 := by
  rw [rowAt, dif_neg (by decide : ¬ 519 < 6), entry_519_checked]
  change forkRow [placeRow ⟨498, 0, 4, 3⟩ (rowAt 498), placeRow ⟨311, 4, 3, 4⟩ (rowAt 311), placeRow ⟨38, 1, 4, 5⟩ (rowAt 38), placeRow ⟨408, 0, 3, 4⟩ (rowAt 408)] = data_519
  rw [row_498, row_311, row_38, row_408]
  apply row_ext <;> decide +kernel
theorem entry_good_519 : EntryGood 519 := by
  unfold EntryGood
  rw [entry_519_checked]
  decide +kernel
theorem good_519 : Good (rowAt 519) := by
  rw [row_519]
  unfold Good
  decide +kernel

theorem block16_group00_piece01_correct : (rowAt 516 = data_516 ∧ Good (rowAt 516) ∧ EntryGood 516) ∧ (rowAt 517 = data_517 ∧ Good (rowAt 517) ∧ EntryGood 517) ∧ (rowAt 518 = data_518 ∧ Good (rowAt 518) ∧ EntryGood 518) ∧ (rowAt 519 = data_519 ∧ Good (rowAt 519) ∧ EntryGood 519) ∧ True := by
  exact ⟨⟨row_516, good_516, entry_good_516⟩, ⟨row_517, good_517, entry_good_517⟩, ⟨row_518, good_518, entry_good_518⟩, ⟨row_519, good_519, entry_good_519⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
