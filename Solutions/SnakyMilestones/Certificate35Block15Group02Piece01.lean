import Solutions.SnakyMilestones.Certificate35Block15Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_500_checked : entryAt 500 = entry_500 := by
  rw [entry_chunk_24 14 (by decide)]
  decide +kernel
theorem row_500 : rowAt 500 = data_500 := by
  rw [rowAt, dif_neg (by decide : ¬ 500 < 6), entry_500_checked]
  change forkRow [placeRow ⟨1, 5, 3, 6⟩ (rowAt 1), placeRow ⟨351, 0, 5, 4⟩ (rowAt 351)] = data_500
  rw [row_1, row_351]
  apply row_ext <;> decide +kernel
theorem entry_good_500 : EntryGood 500 := by
  unfold EntryGood
  rw [entry_500_checked]
  decide +kernel
theorem good_500 : Good (rowAt 500) := by
  rw [row_500]
  unfold Good
  decide +kernel

theorem entry_501_checked : entryAt 501 = entry_501 := by
  rw [entry_chunk_24 15 (by decide)]
  decide +kernel
theorem row_501 : rowAt 501 = data_501 := by
  rw [rowAt, dif_neg (by decide : ¬ 501 < 6), entry_501_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨316, 0, 1, 3⟩ (rowAt 316)] = data_501
  rw [row_6, row_316]
  apply row_ext <;> decide +kernel
theorem entry_good_501 : EntryGood 501 := by
  unfold EntryGood
  rw [entry_501_checked]
  decide +kernel
theorem good_501 : Good (rowAt 501) := by
  rw [row_501]
  unfold Good
  decide +kernel

theorem entry_502_checked : entryAt 502 = entry_502 := by
  rw [entry_chunk_24 16 (by decide)]
  decide +kernel
theorem row_502 : rowAt 502 = data_502 := by
  rw [rowAt, dif_neg (by decide : ¬ 502 < 6), entry_502_checked]
  change forkRow [placeRow ⟨215, 6, 2, 3⟩ (rowAt 215), placeRow ⟨232, 0, 4, 3⟩ (rowAt 232), placeRow ⟨192, 7, 1, 4⟩ (rowAt 192), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173), placeRow ⟨271, 2, 2, 3⟩ (rowAt 271)] = data_502
  rw [row_215, row_232, row_192, row_173, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_502 : EntryGood 502 := by
  unfold EntryGood
  rw [entry_502_checked]
  decide +kernel
theorem good_502 : Good (rowAt 502) := by
  rw [row_502]
  unfold Good
  decide +kernel

theorem entry_503_checked : entryAt 503 = entry_503 := by
  rw [entry_chunk_24 17 (by decide)]
  decide +kernel
theorem row_503 : rowAt 503 = data_503 := by
  rw [rowAt, dif_neg (by decide : ¬ 503 < 6), entry_503_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨420, 1, 7, 2⟩ (rowAt 420), placeRow ⟨419, 1, 7, 4⟩ (rowAt 419)] = data_503
  rw [row_63, row_55, row_420, row_419]
  apply row_ext <;> decide +kernel
theorem entry_good_503 : EntryGood 503 := by
  unfold EntryGood
  rw [entry_503_checked]
  decide +kernel
theorem good_503 : Good (rowAt 503) := by
  rw [row_503]
  unfold Good
  decide +kernel

theorem block15_group02_piece01_correct : (rowAt 500 = data_500 ∧ Good (rowAt 500) ∧ EntryGood 500) ∧ (rowAt 501 = data_501 ∧ Good (rowAt 501) ∧ EntryGood 501) ∧ (rowAt 502 = data_502 ∧ Good (rowAt 502) ∧ EntryGood 502) ∧ (rowAt 503 = data_503 ∧ Good (rowAt 503) ∧ EntryGood 503) ∧ True := by
  exact ⟨⟨row_500, good_500, entry_good_500⟩, ⟨row_501, good_501, entry_good_501⟩, ⟨row_502, good_502, entry_good_502⟩, ⟨row_503, good_503, entry_good_503⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
