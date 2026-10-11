import Solutions.SnakyMilestones.Certificate35Block17Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_548_checked : entryAt 548 = entry_548 := by
  rw [entry_chunk_27 2 (by decide)]
  decide +kernel
theorem row_548 : rowAt 548 = data_548 := by
  rw [rowAt, dif_neg (by decide : ¬ 548 < 6), entry_548_checked]
  change forkRow [placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨541, 0, 4, 5⟩ (rowAt 541), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_548
  rw [row_426, row_541, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_548 : EntryGood 548 := by
  unfold EntryGood
  rw [entry_548_checked]
  decide +kernel
theorem good_548 : Good (rowAt 548) := by
  rw [row_548]
  unfold Good
  decide +kernel

theorem entry_549_checked : entryAt 549 = entry_549 := by
  rw [entry_chunk_27 3 (by decide)]
  decide +kernel
theorem row_549 : rowAt 549 = data_549 := by
  rw [rowAt, dif_neg (by decide : ¬ 549 < 6), entry_549_checked]
  change forkRow [placeRow ⟨385, 0, 6, 4⟩ (rowAt 385), placeRow ⟨385, 4, 2, 4⟩ (rowAt 385), placeRow ⟨330, 0, 6, 4⟩ (rowAt 330), placeRow ⟨252, 6, 2, 4⟩ (rowAt 252), placeRow ⟨326, 0, 6, 4⟩ (rowAt 326), placeRow ⟨529, 0, 2, 4⟩ (rowAt 529)] = data_549
  rw [row_385, row_330, row_252, row_326, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_549 : EntryGood 549 := by
  unfold EntryGood
  rw [entry_549_checked]
  decide +kernel
theorem good_549 : Good (rowAt 549) := by
  rw [row_549]
  unfold Good
  decide +kernel

theorem entry_550_checked : entryAt 550 = entry_550 := by
  rw [entry_chunk_27 4 (by decide)]
  decide +kernel
theorem row_550 : rowAt 550 = data_550 := by
  rw [rowAt, dif_neg (by decide : ¬ 550 < 6), entry_550_checked]
  change forkRow [placeRow ⟨424, 0, 4, 6⟩ (rowAt 424), placeRow ⟨172, 7, 4, 2⟩ (rowAt 172), placeRow ⟨215, 1, 5, 5⟩ (rowAt 215), placeRow ⟨456, 7, 4, 2⟩ (rowAt 456)] = data_550
  rw [row_424, row_172, row_215, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_550 : EntryGood 550 := by
  unfold EntryGood
  rw [entry_550_checked]
  decide +kernel
theorem good_550 : Good (rowAt 550) := by
  rw [row_550]
  unfold Good
  decide +kernel

theorem entry_551_checked : entryAt 551 = entry_551 := by
  rw [entry_chunk_27 5 (by decide)]
  decide +kernel
theorem row_551 : rowAt 551 = data_551 := by
  rw [rowAt, dif_neg (by decide : ¬ 551 < 6), entry_551_checked]
  change forkRow [placeRow ⟨300, 6, 4, 3⟩ (rowAt 300), placeRow ⟨172, 7, 4, 3⟩ (rowAt 172), placeRow ⟨319, 3, 5, 7⟩ (rowAt 319), placeRow ⟨527, 4, 5, 7⟩ (rowAt 527), placeRow ⟨176, 5, 4, 3⟩ (rowAt 176)] = data_551
  rw [row_300, row_172, row_319, row_527, row_176]
  apply row_ext <;> decide +kernel
theorem entry_good_551 : EntryGood 551 := by
  unfold EntryGood
  rw [entry_551_checked]
  decide +kernel
theorem good_551 : Good (rowAt 551) := by
  rw [row_551]
  unfold Good
  decide +kernel

theorem block17_group00_piece01_correct : (rowAt 548 = data_548 ∧ Good (rowAt 548) ∧ EntryGood 548) ∧ (rowAt 549 = data_549 ∧ Good (rowAt 549) ∧ EntryGood 549) ∧ (rowAt 550 = data_550 ∧ Good (rowAt 550) ∧ EntryGood 550) ∧ (rowAt 551 = data_551 ∧ Good (rowAt 551) ∧ EntryGood 551) ∧ True := by
  exact ⟨⟨row_548, good_548, entry_good_548⟩, ⟨row_549, good_549, entry_good_549⟩, ⟨row_550, good_550, entry_good_550⟩, ⟨row_551, good_551, entry_good_551⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
