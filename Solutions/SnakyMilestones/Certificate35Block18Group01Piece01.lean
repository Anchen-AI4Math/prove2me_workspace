import Solutions.SnakyMilestones.Certificate35Block18Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_583_checked : entryAt 583 = entry_583 := by
  rw [entry_chunk_28 17 (by decide)]
  decide +kernel
theorem row_583 : rowAt 583 = data_583 := by
  rw [rowAt, dif_neg (by decide : ¬ 583 < 6), entry_583_checked]
  change forkRow [placeRow ⟨25, 5, 4, 3⟩ (rowAt 25), placeRow ⟨525, 0, 5, 4⟩ (rowAt 525), placeRow ⟨582, 0, 2, 8⟩ (rowAt 582), placeRow ⟨221, 3, 3, 7⟩ (rowAt 221)] = data_583
  rw [row_25, row_525, row_582, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_583 : EntryGood 583 := by
  unfold EntryGood
  rw [entry_583_checked]
  decide +kernel
theorem good_583 : Good (rowAt 583) := by
  rw [row_583]
  unfold Good
  decide +kernel

theorem entry_584_checked : entryAt 584 = entry_584 := by
  rw [entry_chunk_28 18 (by decide)]
  decide +kernel
theorem row_584 : rowAt 584 = data_584 := by
  rw [rowAt, dif_neg (by decide : ¬ 584 < 6), entry_584_checked]
  change forkRow [placeRow ⟨263, 1, 4, 5⟩ (rowAt 263), placeRow ⟨236, 4, 3, 5⟩ (rowAt 236), placeRow ⟨548, 3, 3, 4⟩ (rowAt 548), placeRow ⟨295, 3, 4, 5⟩ (rowAt 295), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨173, 1, 4, 5⟩ (rowAt 173)] = data_584
  rw [row_263, row_236, row_548, row_295, row_577, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_584 : EntryGood 584 := by
  unfold EntryGood
  rw [entry_584_checked]
  decide +kernel
theorem good_584 : Good (rowAt 584) := by
  rw [row_584]
  unfold Good
  decide +kernel

theorem entry_585_checked : entryAt 585 = entry_585 := by
  rw [entry_chunk_28 19 (by decide)]
  decide +kernel
theorem row_585 : rowAt 585 = data_585 := by
  rw [rowAt, dif_neg (by decide : ¬ 585 < 6), entry_585_checked]
  change forkRow [placeRow ⟨236, 2, 5, 1⟩ (rowAt 236), placeRow ⟨300, 4, 4, 5⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨183, 3, 4, 5⟩ (rowAt 183), placeRow ⟨527, 6, 5, 1⟩ (rowAt 527)] = data_585
  rw [row_236, row_300, row_479, row_577, row_183, row_527]
  apply row_ext <;> decide +kernel
theorem entry_good_585 : EntryGood 585 := by
  unfold EntryGood
  rw [entry_585_checked]
  decide +kernel
theorem good_585 : Good (rowAt 585) := by
  rw [row_585]
  unfold Good
  decide +kernel

theorem entry_586_checked : entryAt 586 = entry_586 := by
  rw [entry_chunk_29 0 (by decide)]
  decide +kernel
theorem row_586 : rowAt 586 = data_586 := by
  rw [rowAt, dif_neg (by decide : ¬ 586 < 6), entry_586_checked]
  change forkRow [placeRow ⟨465, 4, 4, 5⟩ (rowAt 465), placeRow ⟨558, 1, 4, 5⟩ (rowAt 558), placeRow ⟨385, 1, 4, 5⟩ (rowAt 385), placeRow ⟨379, 4, 4, 5⟩ (rowAt 379), placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨469, 2, 4, 5⟩ (rowAt 469), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467), placeRow ⟨527, 4, 5, 5⟩ (rowAt 527), placeRow ⟨553, 0, 4, 5⟩ (rowAt 553), placeRow ⟨552, 1, 4, 5⟩ (rowAt 552), placeRow ⟨555, 1, 4, 5⟩ (rowAt 555), placeRow ⟨564, 0, 6, 4⟩ (rowAt 564), placeRow ⟨583, 0, 5, 2⟩ (rowAt 583)] = data_586
  rw [row_465, row_558, row_385, row_379, row_524, row_469, row_467, row_527, row_553, row_552, row_555, row_564, row_583]
  apply row_ext <;> decide +kernel
theorem entry_good_586 : EntryGood 586 := by
  unfold EntryGood
  rw [entry_586_checked]
  decide +kernel
theorem good_586 : Good (rowAt 586) := by
  rw [row_586]
  unfold Good
  decide +kernel

theorem block18_group01_piece01_correct : (rowAt 583 = data_583 ∧ Good (rowAt 583) ∧ EntryGood 583) ∧ (rowAt 584 = data_584 ∧ Good (rowAt 584) ∧ EntryGood 584) ∧ (rowAt 585 = data_585 ∧ Good (rowAt 585) ∧ EntryGood 585) ∧ (rowAt 586 = data_586 ∧ Good (rowAt 586) ∧ EntryGood 586) ∧ True := by
  exact ⟨⟨row_583, good_583, entry_good_583⟩, ⟨row_584, good_584, entry_good_584⟩, ⟨row_585, good_585, entry_good_585⟩, ⟨row_586, good_586, entry_good_586⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
