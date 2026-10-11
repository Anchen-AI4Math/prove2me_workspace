import Solutions.SnakyMilestones.Certificate35Block17Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_564_checked : entryAt 564 = entry_564 := by
  rw [entry_chunk_27 18 (by decide)]
  decide +kernel
theorem row_564 : rowAt 564 = data_564 := by
  rw [rowAt, dif_neg (by decide : ¬ 564 < 6), entry_564_checked]
  change forkRow [placeRow ⟨560, 0, 4, 3⟩ (rowAt 560), placeRow ⟨421, 0, 3, 4⟩ (rowAt 421), placeRow ⟨401, 1, 3, 4⟩ (rowAt 401), placeRow ⟨340, 3, 3, 4⟩ (rowAt 340), placeRow ⟨509, 0, 3, 4⟩ (rowAt 509), placeRow ⟨528, 0, 4, 3⟩ (rowAt 528), placeRow ⟨423, 5, 4, 3⟩ (rowAt 423), placeRow ⟨425, 5, 4, 3⟩ (rowAt 425), placeRow ⟨336, 0, 3, 4⟩ (rowAt 336)] = data_564
  rw [row_560, row_421, row_401, row_340, row_509, row_528, row_423, row_425, row_336]
  apply row_ext <;> decide +kernel
theorem entry_good_564 : EntryGood 564 := by
  unfold EntryGood
  rw [entry_564_checked]
  decide +kernel
theorem good_564 : Good (rowAt 564) := by
  rw [row_564]
  unfold Good
  decide +kernel

theorem entry_565_checked : entryAt 565 = entry_565 := by
  rw [entry_chunk_27 19 (by decide)]
  decide +kernel
theorem row_565 : rowAt 565 = data_565 := by
  rw [rowAt, dif_neg (by decide : ¬ 565 < 6), entry_565_checked]
  change forkRow [placeRow ⟨443, 4, 4, 5⟩ (rowAt 443), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨459, 0, 5, 5⟩ (rowAt 459), placeRow ⟨144, 4, 3, 4⟩ (rowAt 144)] = data_565
  rw [row_443, row_131, row_538, row_459, row_144]
  apply row_ext <;> decide +kernel
theorem entry_good_565 : EntryGood 565 := by
  unfold EntryGood
  rw [entry_565_checked]
  decide +kernel
theorem good_565 : Good (rowAt 565) := by
  rw [row_565]
  unfold Good
  decide +kernel

theorem entry_566_checked : entryAt 566 = entry_566 := by
  rw [entry_chunk_28 0 (by decide)]
  decide +kernel
theorem row_566 : rowAt 566 = data_566 := by
  rw [rowAt, dif_neg (by decide : ¬ 566 < 6), entry_566_checked]
  change forkRow [placeRow ⟨314, 0, 3, 4⟩ (rowAt 314), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504)] = data_566
  rw [row_314, row_180, row_442, row_466, row_504]
  apply row_ext <;> decide +kernel
theorem entry_good_566 : EntryGood 566 := by
  unfold EntryGood
  rw [entry_566_checked]
  decide +kernel
theorem good_566 : Good (rowAt 566) := by
  rw [row_566]
  unfold Good
  decide +kernel

theorem entry_567_checked : entryAt 567 = entry_567 := by
  rw [entry_chunk_28 1 (by decide)]
  decide +kernel
theorem row_567 : rowAt 567 = data_567 := by
  rw [rowAt, dif_neg (by decide : ¬ 567 < 6), entry_567_checked]
  change forkRow [placeRow ⟨21, 1, 4, 3⟩ (rowAt 21), placeRow ⟨561, 0, 6, 4⟩ (rowAt 561), placeRow ⟨500, 4, 3, 1⟩ (rowAt 500)] = data_567
  rw [row_21, row_561, row_500]
  apply row_ext <;> decide +kernel
theorem entry_good_567 : EntryGood 567 := by
  unfold EntryGood
  rw [entry_567_checked]
  decide +kernel
theorem good_567 : Good (rowAt 567) := by
  rw [row_567]
  unfold Good
  decide +kernel

theorem block17_group02_piece01_correct : (rowAt 564 = data_564 ∧ Good (rowAt 564) ∧ EntryGood 564) ∧ (rowAt 565 = data_565 ∧ Good (rowAt 565) ∧ EntryGood 565) ∧ (rowAt 566 = data_566 ∧ Good (rowAt 566) ∧ EntryGood 566) ∧ (rowAt 567 = data_567 ∧ Good (rowAt 567) ∧ EntryGood 567) ∧ True := by
  exact ⟨⟨row_564, good_564, entry_good_564⟩, ⟨row_565, good_565, entry_good_565⟩, ⟨row_566, good_566, entry_good_566⟩, ⟨row_567, good_567, entry_good_567⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
