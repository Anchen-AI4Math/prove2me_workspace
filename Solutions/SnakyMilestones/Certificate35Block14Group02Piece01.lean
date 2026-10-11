import Solutions.SnakyMilestones.Certificate35Block14Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_468_checked : entryAt 468 = entry_468 := by
  rw [entry_chunk_23 2 (by decide)]
  decide +kernel
theorem row_468 : rowAt 468 = data_468 := by
  rw [rowAt, dif_neg (by decide : ¬ 468 < 6), entry_468_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨464, 0, 4, 7⟩ (rowAt 464)] = data_468
  rw [row_6, row_464]
  apply row_ext <;> decide +kernel
theorem entry_good_468 : EntryGood 468 := by
  unfold EntryGood
  rw [entry_468_checked]
  decide +kernel
theorem good_468 : Good (rowAt 468) := by
  rw [row_468]
  unfold Good
  decide +kernel

theorem entry_469_checked : entryAt 469 = entry_469 := by
  rw [entry_chunk_23 3 (by decide)]
  decide +kernel
theorem row_469 : rowAt 469 = data_469 := by
  rw [rowAt, dif_neg (by decide : ¬ 469 < 6), entry_469_checked]
  change forkRow [placeRow ⟨55, 5, 4, 3⟩ (rowAt 55), placeRow ⟨443, 1, 5, 7⟩ (rowAt 443), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314)] = data_469
  rw [row_55, row_443, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_469 : EntryGood 469 := by
  unfold EntryGood
  rw [entry_469_checked]
  decide +kernel
theorem good_469 : Good (rowAt 469) := by
  rw [row_469]
  unfold Good
  decide +kernel

theorem entry_470_checked : entryAt 470 = entry_470 := by
  rw [entry_chunk_23 4 (by decide)]
  decide +kernel
theorem row_470 : rowAt 470 = data_470 := by
  rw [rowAt, dif_neg (by decide : ¬ 470 < 6), entry_470_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨468, 0, 4, 2⟩ (rowAt 468)] = data_470
  rw [row_6, row_468]
  apply row_ext <;> decide +kernel
theorem entry_good_470 : EntryGood 470 := by
  unfold EntryGood
  rw [entry_470_checked]
  decide +kernel
theorem good_470 : Good (rowAt 470) := by
  rw [row_470]
  unfold Good
  decide +kernel

theorem entry_471_checked : entryAt 471 = entry_471 := by
  rw [entry_chunk_23 5 (by decide)]
  decide +kernel
theorem row_471 : rowAt 471 = data_471 := by
  rw [rowAt, dif_neg (by decide : ¬ 471 < 6), entry_471_checked]
  change forkRow [placeRow ⟨6, 5, 4, 3⟩ (rowAt 6), placeRow ⟨466, 0, 5, 6⟩ (rowAt 466)] = data_471
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_471 : EntryGood 471 := by
  unfold EntryGood
  rw [entry_471_checked]
  decide +kernel
theorem good_471 : Good (rowAt 471) := by
  rw [row_471]
  unfold Good
  decide +kernel

theorem block14_group02_piece01_correct : (rowAt 468 = data_468 ∧ Good (rowAt 468) ∧ EntryGood 468) ∧ (rowAt 469 = data_469 ∧ Good (rowAt 469) ∧ EntryGood 469) ∧ (rowAt 470 = data_470 ∧ Good (rowAt 470) ∧ EntryGood 470) ∧ (rowAt 471 = data_471 ∧ Good (rowAt 471) ∧ EntryGood 471) ∧ True := by
  exact ⟨⟨row_468, good_468, entry_good_468⟩, ⟨row_469, good_469, entry_good_469⟩, ⟨row_470, good_470, entry_good_470⟩, ⟨row_471, good_471, entry_good_471⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
