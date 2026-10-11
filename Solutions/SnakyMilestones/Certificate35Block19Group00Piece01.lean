import Solutions.SnakyMilestones.Certificate35Block19Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_593_checked : entryAt 593 = entry_593 := by
  rw [entry_chunk_29 7 (by decide)]
  decide +kernel
theorem row_593 : rowAt 593 = data_593 := by
  rw [rowAt, dif_neg (by decide : ¬ 593 < 6), entry_593_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_593
  rw [row_2, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_593 : EntryGood 593 := by
  unfold EntryGood
  rw [entry_593_checked]
  decide +kernel
theorem good_593 : Good (rowAt 593) := by
  rw [row_593]
  unfold Good
  decide +kernel

theorem entry_594_checked : entryAt 594 = entry_594 := by
  rw [entry_chunk_29 8 (by decide)]
  decide +kernel
theorem row_594 : rowAt 594 = data_594 := by
  rw [rowAt, dif_neg (by decide : ¬ 594 < 6), entry_594_checked]
  change forkRow [placeRow ⟨30, 1, 4, 3⟩ (rowAt 30), placeRow ⟨476, 1, 4, 3⟩ (rowAt 476), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_594
  rw [row_30, row_476, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_594 : EntryGood 594 := by
  unfold EntryGood
  rw [entry_594_checked]
  decide +kernel
theorem good_594 : Good (rowAt 594) := by
  rw [row_594]
  unfold Good
  decide +kernel

theorem entry_595_checked : entryAt 595 = entry_595 := by
  rw [entry_chunk_29 9 (by decide)]
  decide +kernel
theorem row_595 : rowAt 595 = data_595 := by
  rw [rowAt, dif_neg (by decide : ¬ 595 < 6), entry_595_checked]
  change forkRow [placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨586, 1, 5, 4⟩ (rowAt 586), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨551, 1, 2, 4⟩ (rowAt 551), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406), placeRow ⟨572, 0, 2, 4⟩ (rowAt 572)] = data_595
  rw [row_460, row_586, row_411, row_551, row_406, row_572]
  apply row_ext <;> decide +kernel
theorem entry_good_595 : EntryGood 595 := by
  unfold EntryGood
  rw [entry_595_checked]
  decide +kernel
theorem good_595 : Good (rowAt 595) := by
  rw [row_595]
  unfold Good
  decide +kernel

theorem entry_596_checked : entryAt 596 = entry_596 := by
  rw [entry_chunk_29 10 (by decide)]
  decide +kernel
theorem row_596 : rowAt 596 = data_596 := by
  rw [rowAt, dif_neg (by decide : ¬ 596 < 6), entry_596_checked]
  change forkRow [placeRow ⟨385, 5, 4, 2⟩ (rowAt 385), placeRow ⟨592, 0, 5, 6⟩ (rowAt 592), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330), placeRow ⟨529, 5, 4, 6⟩ (rowAt 529), placeRow ⟨385, 1, 4, 6⟩ (rowAt 385), placeRow ⟨330, 5, 4, 2⟩ (rowAt 330)] = data_596
  rw [row_385, row_592, row_330, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_596 : EntryGood 596 := by
  unfold EntryGood
  rw [entry_596_checked]
  decide +kernel
theorem good_596 : Good (rowAt 596) := by
  rw [row_596]
  unfold Good
  decide +kernel

theorem block19_group00_piece01_correct : (rowAt 593 = data_593 ∧ Good (rowAt 593) ∧ EntryGood 593) ∧ (rowAt 594 = data_594 ∧ Good (rowAt 594) ∧ EntryGood 594) ∧ (rowAt 595 = data_595 ∧ Good (rowAt 595) ∧ EntryGood 595) ∧ (rowAt 596 = data_596 ∧ Good (rowAt 596) ∧ EntryGood 596) ∧ True := by
  exact ⟨⟨row_593, good_593, entry_good_593⟩, ⟨row_594, good_594, entry_good_594⟩, ⟨row_595, good_595, entry_good_595⟩, ⟨row_596, good_596, entry_good_596⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
