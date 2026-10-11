import Solutions.SnakyMilestones.Certificate35Block14Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_460_checked : entryAt 460 = entry_460 := by
  rw [entry_chunk_22 14 (by decide)]
  decide +kernel
theorem row_460 : rowAt 460 = data_460 := by
  rw [rowAt, dif_neg (by decide : ¬ 460 < 6), entry_460_checked]
  change forkRow [placeRow ⟨183, 6, 1, 4⟩ (rowAt 183), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨282, 4, 1, 4⟩ (rowAt 282), placeRow ⟨246, 2, 5, 4⟩ (rowAt 246), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨220, 2, 5, 4⟩ (rowAt 220)] = data_460
  rw [row_183, row_173, row_295, row_282, row_246, row_263, row_220]
  apply row_ext <;> decide +kernel
theorem entry_good_460 : EntryGood 460 := by
  unfold EntryGood
  rw [entry_460_checked]
  decide +kernel
theorem good_460 : Good (rowAt 460) := by
  rw [row_460]
  unfold Good
  decide +kernel

theorem entry_461_checked : entryAt 461 = entry_461 := by
  rw [entry_chunk_22 15 (by decide)]
  decide +kernel
theorem row_461 : rowAt 461 = data_461 := by
  rw [rowAt, dif_neg (by decide : ¬ 461 < 6), entry_461_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨458, 0, 6, 4⟩ (rowAt 458)] = data_461
  rw [row_4, row_458]
  apply row_ext <;> decide +kernel
theorem entry_good_461 : EntryGood 461 := by
  unfold EntryGood
  rw [entry_461_checked]
  decide +kernel
theorem good_461 : Good (rowAt 461) := by
  rw [row_461]
  unfold Good
  decide +kernel

theorem entry_462_checked : entryAt 462 = entry_462 := by
  rw [entry_chunk_22 16 (by decide)]
  decide +kernel
theorem row_462 : rowAt 462 = data_462 := by
  rw [rowAt, dif_neg (by decide : ¬ 462 < 6), entry_462_checked]
  change forkRow [placeRow ⟨452, 0, 3, 2⟩ (rowAt 452), placeRow ⟨86, 0, 5, 4⟩ (rowAt 86), placeRow ⟨328, 1, 5, 4⟩ (rowAt 328)] = data_462
  rw [row_452, row_86, row_328]
  apply row_ext <;> decide +kernel
theorem entry_good_462 : EntryGood 462 := by
  unfold EntryGood
  rw [entry_462_checked]
  decide +kernel
theorem good_462 : Good (rowAt 462) := by
  rw [row_462]
  unfold Good
  decide +kernel

theorem entry_463_checked : entryAt 463 = entry_463 := by
  rw [entry_chunk_22 17 (by decide)]
  decide +kernel
theorem row_463 : rowAt 463 = data_463 := by
  rw [rowAt, dif_neg (by decide : ¬ 463 < 6), entry_463_checked]
  change forkRow [placeRow ⟨170, 0, 6, 3⟩ (rowAt 170), placeRow ⟨76, 1, 3, 2⟩ (rowAt 76), placeRow ⟨447, 0, 5, 4⟩ (rowAt 447)] = data_463
  rw [row_170, row_76, row_447]
  apply row_ext <;> decide +kernel
theorem entry_good_463 : EntryGood 463 := by
  unfold EntryGood
  rw [entry_463_checked]
  decide +kernel
theorem good_463 : Good (rowAt 463) := by
  rw [row_463]
  unfold Good
  decide +kernel

theorem block14_group01_piece01_correct : (rowAt 460 = data_460 ∧ Good (rowAt 460) ∧ EntryGood 460) ∧ (rowAt 461 = data_461 ∧ Good (rowAt 461) ∧ EntryGood 461) ∧ (rowAt 462 = data_462 ∧ Good (rowAt 462) ∧ EntryGood 462) ∧ (rowAt 463 = data_463 ∧ Good (rowAt 463) ∧ EntryGood 463) ∧ True := by
  exact ⟨⟨row_460, good_460, entry_good_460⟩, ⟨row_461, good_461, entry_good_461⟩, ⟨row_462, good_462, entry_good_462⟩, ⟨row_463, good_463, entry_good_463⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
