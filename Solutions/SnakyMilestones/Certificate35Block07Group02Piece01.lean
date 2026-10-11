import Solutions.SnakyMilestones.Certificate35Block07Group02Piece00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_244_checked : entryAt 244 = entry_244 := by
  rw [entry_chunk_11 18 (by decide)]
  decide +kernel
theorem row_244 : rowAt 244 = data_244 := by
  rw [rowAt, dif_neg (by decide : ¬ 244 < 6), entry_244_checked]
  change forkRow [placeRow ⟨99, 4, 2, 5⟩ (rowAt 99), placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨11, 7, 3, 3⟩ (rowAt 11), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173)] = data_244
  rw [row_99, row_11, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_244 : EntryGood 244 := by
  unfold EntryGood
  rw [entry_244_checked]
  decide +kernel
theorem good_244 : Good (rowAt 244) := by
  rw [row_244]
  unfold Good
  decide +kernel

theorem entry_245_checked : entryAt 245 = entry_245 := by
  rw [entry_chunk_11 19 (by decide)]
  decide +kernel
theorem row_245 : rowAt 245 = data_245 := by
  rw [rowAt, dif_neg (by decide : ¬ 245 < 6), entry_245_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨175, 4, 0, 4⟩ (rowAt 175), placeRow ⟨143, 6, 4, 5⟩ (rowAt 143), placeRow ⟨186, 6, 0, 4⟩ (rowAt 186)] = data_245
  rw [row_64, row_175, row_143, row_186]
  apply row_ext <;> decide +kernel
theorem entry_good_245 : EntryGood 245 := by
  unfold EntryGood
  rw [entry_245_checked]
  decide +kernel
theorem good_245 : Good (rowAt 245) := by
  rw [row_245]
  unfold Good
  decide +kernel

theorem entry_246_checked : entryAt 246 = entry_246 := by
  rw [entry_chunk_12 0 (by decide)]
  decide +kernel
theorem row_246 : rowAt 246 = data_246 := by
  rw [rowAt, dif_neg (by decide : ¬ 246 < 6), entry_246_checked]
  change forkRow [placeRow ⟨64, 6, 4, 5⟩ (rowAt 64), placeRow ⟨175, 2, 5, 4⟩ (rowAt 175), placeRow ⟨186, 0, 5, 4⟩ (rowAt 186), placeRow ⟨143, 0, 1, 3⟩ (rowAt 143)] = data_246
  rw [row_64, row_175, row_186, row_143]
  apply row_ext <;> decide +kernel
theorem entry_good_246 : EntryGood 246 := by
  unfold EntryGood
  rw [entry_246_checked]
  decide +kernel
theorem good_246 : Good (rowAt 246) := by
  rw [row_246]
  unfold Good
  decide +kernel

theorem entry_247_checked : entryAt 247 = entry_247 := by
  rw [entry_chunk_12 1 (by decide)]
  decide +kernel
theorem row_247 : rowAt 247 = data_247 := by
  rw [rowAt, dif_neg (by decide : ¬ 247 < 6), entry_247_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨229, 0, 4, 5⟩ (rowAt 229)] = data_247
  rw [row_6, row_229]
  apply row_ext <;> decide +kernel
theorem entry_good_247 : EntryGood 247 := by
  unfold EntryGood
  rw [entry_247_checked]
  decide +kernel
theorem good_247 : Good (rowAt 247) := by
  rw [row_247]
  unfold Good
  decide +kernel

theorem block07_group02_piece01_correct : (rowAt 244 = data_244 ∧ Good (rowAt 244) ∧ EntryGood 244) ∧ (rowAt 245 = data_245 ∧ Good (rowAt 245) ∧ EntryGood 245) ∧ (rowAt 246 = data_246 ∧ Good (rowAt 246) ∧ EntryGood 246) ∧ (rowAt 247 = data_247 ∧ Good (rowAt 247) ∧ EntryGood 247) ∧ True := by
  exact ⟨⟨row_244, good_244, entry_good_244⟩, ⟨row_245, good_245, entry_good_245⟩, ⟨row_246, good_246, entry_good_246⟩, ⟨row_247, good_247, entry_good_247⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
