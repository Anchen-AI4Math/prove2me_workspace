import Solutions.SnakyMilestones.Certificate35Block12Group00Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_388_checked : entryAt 388 = entry_388 := by
  rw [entry_chunk_19 2 (by decide)]
  decide +kernel
theorem row_388 : rowAt 388 = data_388 := by
  rw [rowAt, dif_neg (by decide : ¬ 388 < 6), entry_388_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨374, 0, 3, 4⟩ (rowAt 374)] = data_388
  rw [row_6, row_374]
  apply row_ext <;> decide +kernel
theorem entry_good_388 : EntryGood 388 := by
  unfold EntryGood
  rw [entry_388_checked]
  decide +kernel
theorem good_388 : Good (rowAt 388) := by
  rw [row_388]
  unfold Good
  decide +kernel

theorem entry_389_checked : entryAt 389 = entry_389 := by
  rw [entry_chunk_19 3 (by decide)]
  decide +kernel
theorem row_389 : rowAt 389 = data_389 := by
  rw [rowAt, dif_neg (by decide : ¬ 389 < 6), entry_389_checked]
  change forkRow [placeRow ⟨197, 5, 4, 1⟩ (rowAt 197), placeRow ⟨215, 7, 3, 2⟩ (rowAt 215), placeRow ⟨271, 3, 3, 2⟩ (rowAt 271), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨192, 6, 4, 1⟩ (rowAt 192)] = data_389
  rw [row_197, row_215, row_271, row_236, row_192]
  apply row_ext <;> decide +kernel
theorem entry_good_389 : EntryGood 389 := by
  unfold EntryGood
  rw [entry_389_checked]
  decide +kernel
theorem good_389 : Good (rowAt 389) := by
  rw [row_389]
  unfold Good
  decide +kernel

theorem entry_390_checked : entryAt 390 = entry_390 := by
  rw [entry_chunk_19 4 (by decide)]
  decide +kernel
theorem row_390 : rowAt 390 = data_390 := by
  rw [rowAt, dif_neg (by decide : ¬ 390 < 6), entry_390_checked]
  change forkRow [placeRow ⟨372, 2, 5, 0⟩ (rowAt 372), placeRow ⟨167, 5, 4, 1⟩ (rowAt 167), placeRow ⟨12, 7, 3, 1⟩ (rowAt 12)] = data_390
  rw [row_372, row_167, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_390 : EntryGood 390 := by
  unfold EntryGood
  rw [entry_390_checked]
  decide +kernel
theorem good_390 : Good (rowAt 390) := by
  rw [row_390]
  unfold Good
  decide +kernel

theorem entry_391_checked : entryAt 391 = entry_391 := by
  rw [entry_chunk_19 5 (by decide)]
  decide +kernel
theorem row_391 : rowAt 391 = data_391 := by
  rw [rowAt, dif_neg (by decide : ¬ 391 < 6), entry_391_checked]
  change forkRow [placeRow ⟨6, 5, 5, 1⟩ (rowAt 6), placeRow ⟨388, 0, 3, 5⟩ (rowAt 388)] = data_391
  rw [row_6, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_391 : EntryGood 391 := by
  unfold EntryGood
  rw [entry_391_checked]
  decide +kernel
theorem good_391 : Good (rowAt 391) := by
  rw [row_391]
  unfold Good
  decide +kernel

theorem block12_group00_piece01_correct : (rowAt 388 = data_388 ∧ Good (rowAt 388) ∧ EntryGood 388) ∧ (rowAt 389 = data_389 ∧ Good (rowAt 389) ∧ EntryGood 389) ∧ (rowAt 390 = data_390 ∧ Good (rowAt 390) ∧ EntryGood 390) ∧ (rowAt 391 = data_391 ∧ Good (rowAt 391) ∧ EntryGood 391) ∧ True := by
  exact ⟨⟨row_388, good_388, entry_good_388⟩, ⟨row_389, good_389, entry_good_389⟩, ⟨row_390, good_390, entry_good_390⟩, ⟨row_391, good_391, entry_good_391⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
