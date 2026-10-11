import Solutions.SnakyMilestones.Certificate35Block16Group03Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_540_checked : entryAt 540 = entry_540 := by
  rw [entry_chunk_26 14 (by decide)]
  decide +kernel
theorem row_540 : rowAt 540 = data_540 := by
  rw [rowAt, dif_neg (by decide : ¬ 540 < 6), entry_540_checked]
  change forkRow [placeRow ⟨334, 0, 4, 3⟩ (rowAt 334), placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨88, 3, 4, 3⟩ (rowAt 88), placeRow ⟨536, 0, 5, 4⟩ (rowAt 536)] = data_540
  rw [row_334, row_51, row_88, row_536]
  apply row_ext <;> decide +kernel
theorem entry_good_540 : EntryGood 540 := by
  unfold EntryGood
  rw [entry_540_checked]
  decide +kernel
theorem good_540 : Good (rowAt 540) := by
  rw [row_540]
  unfold Good
  decide +kernel

theorem entry_541_checked : entryAt 541 = entry_541 := by
  rw [entry_chunk_26 15 (by decide)]
  decide +kernel
theorem row_541 : rowAt 541 = data_541 := by
  rw [rowAt, dif_neg (by decide : ¬ 541 < 6), entry_541_checked]
  change forkRow [placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨142, 7, 4, 1⟩ (rowAt 142), placeRow ⟨160, 3, 4, 1⟩ (rowAt 160), placeRow ⟨194, 0, 5, 3⟩ (rowAt 194), placeRow ⟨501, 4, 1, 2⟩ (rowAt 501), placeRow ⟨412, 0, 5, 3⟩ (rowAt 412)] = data_541
  rw [row_236, row_142, row_160, row_194, row_501, row_412]
  apply row_ext <;> decide +kernel
theorem entry_good_541 : EntryGood 541 := by
  unfold EntryGood
  rw [entry_541_checked]
  decide +kernel
theorem good_541 : Good (rowAt 541) := by
  rw [row_541]
  unfold Good
  decide +kernel

theorem entry_542_checked : entryAt 542 = entry_542 := by
  rw [entry_chunk_26 16 (by decide)]
  decide +kernel
theorem row_542 : rowAt 542 = data_542 := by
  rw [rowAt, dif_neg (by decide : ¬ 542 < 6), entry_542_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442)] = data_542
  rw [row_6, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_542 : EntryGood 542 := by
  unfold EntryGood
  rw [entry_542_checked]
  decide +kernel
theorem good_542 : Good (rowAt 542) := by
  rw [row_542]
  unfold Good
  decide +kernel

theorem entry_543_checked : entryAt 543 = entry_543 := by
  rw [entry_chunk_26 17 (by decide)]
  decide +kernel
theorem row_543 : rowAt 543 = data_543 := by
  rw [rowAt, dif_neg (by decide : ¬ 543 < 6), entry_543_checked]
  change forkRow [placeRow ⟨493, 3, 2, 6⟩ (rowAt 493), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318)] = data_543
  rw [row_493, row_107, row_318]
  apply row_ext <;> decide +kernel
theorem entry_good_543 : EntryGood 543 := by
  unfold EntryGood
  rw [entry_543_checked]
  decide +kernel
theorem good_543 : Good (rowAt 543) := by
  rw [row_543]
  unfold Good
  decide +kernel


theorem block16_group03_piece01_correct : (rowAt 540 = data_540 ∧ Good (rowAt 540) ∧ EntryGood 540) ∧ (rowAt 541 = data_541 ∧ Good (rowAt 541) ∧ EntryGood 541) ∧ (rowAt 542 = data_542 ∧ Good (rowAt 542) ∧ EntryGood 542) ∧ (rowAt 543 = data_543 ∧ Good (rowAt 543) ∧ EntryGood 543) ∧ True := by
  exact ⟨⟨row_540, good_540, entry_good_540⟩, ⟨row_541, good_541, entry_good_541⟩, ⟨row_542, good_542, entry_good_542⟩, ⟨row_543, good_543, entry_good_543⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
