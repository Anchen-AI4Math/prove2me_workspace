import Solutions.SnakyMilestones.Certificate35Block15Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_508_checked : entryAt 508 = entry_508 := by
  rw [entry_chunk_25 2 (by decide)]
  decide +kernel
theorem row_508 : rowAt 508 = data_508 := by
  rw [rowAt, dif_neg (by decide : ¬ 508 < 6), entry_508_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨393, 0, 1, 5⟩ (rowAt 393)] = data_508
  rw [row_6, row_393]
  apply row_ext <;> decide +kernel
theorem entry_good_508 : EntryGood 508 := by
  unfold EntryGood
  rw [entry_508_checked]
  decide +kernel
theorem good_508 : Good (rowAt 508) := by
  rw [row_508]
  unfold Good
  decide +kernel

theorem entry_509_checked : entryAt 509 = entry_509 := by
  rw [entry_chunk_25 3 (by decide)]
  decide +kernel
theorem row_509 : rowAt 509 = data_509 := by
  rw [rowAt, dif_neg (by decide : ¬ 509 < 6), entry_509_checked]
  change forkRow [placeRow ⟨252, 0, 6, 4⟩ (rowAt 252), placeRow ⟨241, 4, 2, 4⟩ (rowAt 241), placeRow ⟨455, 0, 6, 3⟩ (rowAt 455), placeRow ⟨68, 2, 6, 4⟩ (rowAt 68)] = data_509
  rw [row_252, row_241, row_455, row_68]
  apply row_ext <;> decide +kernel
theorem entry_good_509 : EntryGood 509 := by
  unfold EntryGood
  rw [entry_509_checked]
  decide +kernel
theorem good_509 : Good (rowAt 509) := by
  rw [row_509]
  unfold Good
  decide +kernel

theorem entry_510_checked : entryAt 510 = entry_510 := by
  rw [entry_chunk_25 4 (by decide)]
  decide +kernel
theorem row_510 : rowAt 510 = data_510 := by
  rw [rowAt, dif_neg (by decide : ¬ 510 < 6), entry_510_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨508, 0, 7, 4⟩ (rowAt 508)] = data_510
  rw [row_6, row_508]
  apply row_ext <;> decide +kernel
theorem entry_good_510 : EntryGood 510 := by
  unfold EntryGood
  rw [entry_510_checked]
  decide +kernel
theorem good_510 : Good (rowAt 510) := by
  rw [row_510]
  unfold Good
  decide +kernel

theorem entry_511_checked : entryAt 511 = entry_511 := by
  rw [entry_chunk_25 5 (by decide)]
  decide +kernel
theorem row_511 : rowAt 511 = data_511 := by
  rw [rowAt, dif_neg (by decide : ¬ 511 < 6), entry_511_checked]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (rowAt 15), placeRow ⟨331, 0, 5, 3⟩ (rowAt 331), placeRow ⟨380, 4, 2, 4⟩ (rowAt 380)] = data_511
  rw [row_15, row_331, row_380]
  apply row_ext <;> decide +kernel
theorem entry_good_511 : EntryGood 511 := by
  unfold EntryGood
  rw [entry_511_checked]
  decide +kernel
theorem good_511 : Good (rowAt 511) := by
  rw [row_511]
  unfold Good
  decide +kernel


theorem block15_group03_piece01_correct : (rowAt 508 = data_508 ∧ Good (rowAt 508) ∧ EntryGood 508) ∧ (rowAt 509 = data_509 ∧ Good (rowAt 509) ∧ EntryGood 509) ∧ (rowAt 510 = data_510 ∧ Good (rowAt 510) ∧ EntryGood 510) ∧ (rowAt 511 = data_511 ∧ Good (rowAt 511) ∧ EntryGood 511) ∧ True := by
  exact ⟨⟨row_508, good_508, entry_good_508⟩, ⟨row_509, good_509, entry_good_509⟩, ⟨row_510, good_510, entry_good_510⟩, ⟨row_511, good_511, entry_good_511⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
