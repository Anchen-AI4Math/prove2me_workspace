import Solutions.SnakyMilestones.Certificate35Block17Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_556_checked : entryAt 556 = entry_556 := by
  rw [entry_chunk_27 10 (by decide)]
  decide +kernel
theorem row_556 : rowAt 556 = data_556 := by
  rw [rowAt, dif_neg (by decide : ¬ 556 < 6), entry_556_checked]
  change forkRow [placeRow ⟨34, 1, 4, 2⟩ (rowAt 34), placeRow ⟨549, 0, 3, 4⟩ (rowAt 549)] = data_556
  rw [row_34, row_549]
  apply row_ext <;> decide +kernel
theorem entry_good_556 : EntryGood 556 := by
  unfold EntryGood
  rw [entry_556_checked]
  decide +kernel
theorem good_556 : Good (rowAt 556) := by
  rw [row_556]
  unfold Good
  decide +kernel

theorem entry_557_checked : entryAt 557 = entry_557 := by
  rw [entry_chunk_27 11 (by decide)]
  decide +kernel
theorem row_557 : rowAt 557 = data_557 := by
  rw [rowAt, dif_neg (by decide : ¬ 557 < 6), entry_557_checked]
  change forkRow [placeRow ⟨460, 0, 5, 4⟩ (rowAt 460), placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨531, 0, 3, 6⟩ (rowAt 531), placeRow ⟨531, 4, 4, 6⟩ (rowAt 531), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406)] = data_557
  rw [row_460, row_411, row_531, row_406]
  apply row_ext <;> decide +kernel
theorem entry_good_557 : EntryGood 557 := by
  unfold EntryGood
  rw [entry_557_checked]
  decide +kernel
theorem good_557 : Good (rowAt 557) := by
  rw [row_557]
  unfold Good
  decide +kernel

theorem entry_558_checked : entryAt 558 = entry_558 := by
  rw [entry_chunk_27 12 (by decide)]
  decide +kernel
theorem row_558 : rowAt 558 = data_558 := by
  rw [rowAt, dif_neg (by decide : ¬ 558 < 6), entry_558_checked]
  change forkRow [placeRow ⟨180, 5, 5, 4⟩ (rowAt 180), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨442, 1, 5, 4⟩ (rowAt 442)] = data_558
  rw [row_180, row_443, row_513, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_558 : EntryGood 558 := by
  unfold EntryGood
  rw [entry_558_checked]
  decide +kernel
theorem good_558 : Good (rowAt 558) := by
  rw [row_558]
  unfold Good
  decide +kernel

theorem entry_559_checked : entryAt 559 = entry_559 := by
  rw [entry_chunk_27 13 (by decide)]
  decide +kernel
theorem row_559 : rowAt 559 = data_559 := by
  rw [rowAt, dif_neg (by decide : ¬ 559 < 6), entry_559_checked]
  change forkRow [placeRow ⟨228, 4, 5, 2⟩ (rowAt 228), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨538, 5, 4, 5⟩ (rowAt 538)] = data_559
  rw [row_228, row_7, row_155, row_538]
  apply row_ext <;> decide +kernel
theorem entry_good_559 : EntryGood 559 := by
  unfold EntryGood
  rw [entry_559_checked]
  decide +kernel
theorem good_559 : Good (rowAt 559) := by
  rw [row_559]
  unfold Good
  decide +kernel

theorem block17_group01_piece01_correct : (rowAt 556 = data_556 ∧ Good (rowAt 556) ∧ EntryGood 556) ∧ (rowAt 557 = data_557 ∧ Good (rowAt 557) ∧ EntryGood 557) ∧ (rowAt 558 = data_558 ∧ Good (rowAt 558) ∧ EntryGood 558) ∧ (rowAt 559 = data_559 ∧ Good (rowAt 559) ∧ EntryGood 559) ∧ True := by
  exact ⟨⟨row_556, good_556, entry_good_556⟩, ⟨row_557, good_557, entry_good_557⟩, ⟨row_558, good_558, entry_good_558⟩, ⟨row_559, good_559, entry_good_559⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
