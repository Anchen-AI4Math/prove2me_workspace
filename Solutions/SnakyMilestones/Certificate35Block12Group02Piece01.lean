import Solutions.SnakyMilestones.Certificate35Block12Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_404_checked : entryAt 404 = entry_404 := by
  rw [entry_chunk_19 18 (by decide)]
  decide +kernel
theorem row_404 : rowAt 404 = data_404 := by
  rw [rowAt, dif_neg (by decide : ¬ 404 < 6), entry_404_checked]
  change forkRow [placeRow ⟨82, 6, 2, 3⟩ (rowAt 82), placeRow ⟨388, 4, 4, 6⟩ (rowAt 388)] = data_404
  rw [row_82, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_404 : EntryGood 404 := by
  unfold EntryGood
  rw [entry_404_checked]
  decide +kernel
theorem good_404 : Good (rowAt 404) := by
  rw [row_404]
  unfold Good
  decide +kernel

theorem entry_405_checked : entryAt 405 = entry_405 := by
  rw [entry_chunk_19 19 (by decide)]
  decide +kernel
theorem row_405 : rowAt 405 = data_405 := by
  rw [rowAt, dif_neg (by decide : ¬ 405 < 6), entry_405_checked]
  change forkRow [placeRow ⟨391, 0, 4, 3⟩ (rowAt 391), placeRow ⟨301, 0, 5, 2⟩ (rowAt 301), placeRow ⟨42, 1, 4, 3⟩ (rowAt 42)] = data_405
  rw [row_391, row_301, row_42]
  apply row_ext <;> decide +kernel
theorem entry_good_405 : EntryGood 405 := by
  unfold EntryGood
  rw [entry_405_checked]
  decide +kernel
theorem good_405 : Good (rowAt 405) := by
  rw [row_405]
  unfold Good
  decide +kernel

theorem entry_406_checked : entryAt 406 = entry_406 := by
  rw [entry_chunk_20 0 (by decide)]
  decide +kernel
theorem row_406 : rowAt 406 = data_406 := by
  rw [rowAt, dif_neg (by decide : ¬ 406 < 6), entry_406_checked]
  change forkRow [placeRow ⟨295, 1, 4, 5⟩ (rowAt 295), placeRow ⟨172, 7, 4, 1⟩ (rowAt 172), placeRow ⟨245, 3, 4, 5⟩ (rowAt 245), placeRow ⟨197, 5, 4, 1⟩ (rowAt 197), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨176, 3, 4, 5⟩ (rowAt 176), placeRow ⟨364, 2, 4, 1⟩ (rowAt 364)] = data_406
  rw [row_295, row_172, row_245, row_197, row_236, row_176, row_364]
  apply row_ext <;> decide +kernel
theorem entry_good_406 : EntryGood 406 := by
  unfold EntryGood
  rw [entry_406_checked]
  decide +kernel
theorem good_406 : Good (rowAt 406) := by
  rw [row_406]
  unfold Good
  decide +kernel

theorem entry_407_checked : entryAt 407 = entry_407 := by
  rw [entry_chunk_20 1 (by decide)]
  decide +kernel
theorem row_407 : rowAt 407 = data_407 := by
  rw [rowAt, dif_neg (by decide : ¬ 407 < 6), entry_407_checked]
  change forkRow [placeRow ⟨285, 0, 3, 7⟩ (rowAt 285), placeRow ⟨314, 6, 5, 4⟩ (rowAt 314)] = data_407
  rw [row_285, row_314]
  apply row_ext <;> decide +kernel
theorem entry_good_407 : EntryGood 407 := by
  unfold EntryGood
  rw [entry_407_checked]
  decide +kernel
theorem good_407 : Good (rowAt 407) := by
  rw [row_407]
  unfold Good
  decide +kernel

theorem block12_group02_piece01_correct : (rowAt 404 = data_404 ∧ Good (rowAt 404) ∧ EntryGood 404) ∧ (rowAt 405 = data_405 ∧ Good (rowAt 405) ∧ EntryGood 405) ∧ (rowAt 406 = data_406 ∧ Good (rowAt 406) ∧ EntryGood 406) ∧ (rowAt 407 = data_407 ∧ Good (rowAt 407) ∧ EntryGood 407) ∧ True := by
  exact ⟨⟨row_404, good_404, entry_good_404⟩, ⟨row_405, good_405, entry_good_405⟩, ⟨row_406, good_406, entry_good_406⟩, ⟨row_407, good_407, entry_good_407⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
