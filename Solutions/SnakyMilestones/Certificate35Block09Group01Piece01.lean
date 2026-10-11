import Solutions.SnakyMilestones.Certificate35Block09Group01Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_300_checked : entryAt 300 = entry_300 := by
  rw [entry_chunk_14 14 (by decide)]
  decide +kernel
theorem row_300 : rowAt 300 = data_300 := by
  rw [rowAt, dif_neg (by decide : ¬ 300 < 6), entry_300_checked]
  change forkRow [placeRow ⟨64, 3, 5, 1⟩ (rowAt 64), placeRow ⟨240, 2, 5, 1⟩ (rowAt 240), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_300
  rw [row_64, row_240, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_300 : EntryGood 300 := by
  unfold EntryGood
  rw [entry_300_checked]
  decide +kernel
theorem good_300 : Good (rowAt 300) := by
  rw [row_300]
  unfold Good
  decide +kernel

theorem entry_301_checked : entryAt 301 = entry_301 := by
  rw [entry_chunk_14 15 (by decide)]
  decide +kernel
theorem row_301 : rowAt 301 = data_301 := by
  rw [rowAt, dif_neg (by decide : ¬ 301 < 6), entry_301_checked]
  change forkRow [placeRow ⟨59, 0, 5, 4⟩ (rowAt 59), placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨258, 4, 4, 5⟩ (rowAt 258)] = data_301
  rw [row_59, row_57, row_258]
  apply row_ext <;> decide +kernel
theorem entry_good_301 : EntryGood 301 := by
  unfold EntryGood
  rw [entry_301_checked]
  decide +kernel
theorem good_301 : Good (rowAt 301) := by
  rw [row_301]
  unfold Good
  decide +kernel

theorem entry_302_checked : entryAt 302 = entry_302 := by
  rw [entry_chunk_14 16 (by decide)]
  decide +kernel
theorem row_302 : rowAt 302 = data_302 := by
  rw [rowAt, dif_neg (by decide : ¬ 302 < 6), entry_302_checked]
  change forkRow [placeRow ⟨125, 0, 5, 3⟩ (rowAt 125), placeRow ⟨162, 4, 3, 6⟩ (rowAt 162)] = data_302
  rw [row_125, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_302 : EntryGood 302 := by
  unfold EntryGood
  rw [entry_302_checked]
  decide +kernel
theorem good_302 : Good (rowAt 302) := by
  rw [row_302]
  unfold Good
  decide +kernel

theorem entry_303_checked : entryAt 303 = entry_303 := by
  rw [entry_chunk_14 17 (by decide)]
  decide +kernel
theorem row_303 : rowAt 303 = data_303 := by
  rw [rowAt, dif_neg (by decide : ¬ 303 < 6), entry_303_checked]
  change forkRow [placeRow ⟨49, 4, 4, 5⟩ (rowAt 49), placeRow ⟨44, 1, 4, 5⟩ (rowAt 44), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_303
  rw [row_49, row_44, row_63, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_303 : EntryGood 303 := by
  unfold EntryGood
  rw [entry_303_checked]
  decide +kernel
theorem good_303 : Good (rowAt 303) := by
  rw [row_303]
  unfold Good
  decide +kernel

theorem block09_group01_piece01_correct : (rowAt 300 = data_300 ∧ Good (rowAt 300) ∧ EntryGood 300) ∧ (rowAt 301 = data_301 ∧ Good (rowAt 301) ∧ EntryGood 301) ∧ (rowAt 302 = data_302 ∧ Good (rowAt 302) ∧ EntryGood 302) ∧ (rowAt 303 = data_303 ∧ Good (rowAt 303) ∧ EntryGood 303) ∧ True := by
  exact ⟨⟨row_300, good_300, entry_good_300⟩, ⟨row_301, good_301, entry_good_301⟩, ⟨row_302, good_302, entry_good_302⟩, ⟨row_303, good_303, entry_good_303⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
