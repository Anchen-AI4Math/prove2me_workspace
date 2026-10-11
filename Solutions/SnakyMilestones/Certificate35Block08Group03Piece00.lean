import Definitions.Def_Snaky35Cache08
import Solutions.SnakyMilestones.Certificate35Block08Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_280_checked : entryAt 280 = entry_280 := by
  rw [entry_chunk_13 14 (by decide)]
  decide +kernel
theorem row_280 : rowAt 280 = data_280 := by
  rw [rowAt, dif_neg (by decide : ¬ 280 < 6), entry_280_checked]
  change forkRow [placeRow ⟨184, 0, 1, 5⟩ (rowAt 184), placeRow ⟨116, 2, 4, 3⟩ (rowAt 116)] = data_280
  rw [row_184, row_116]
  apply row_ext <;> decide +kernel
theorem entry_good_280 : EntryGood 280 := by
  unfold EntryGood
  rw [entry_280_checked]
  decide +kernel
theorem good_280 : Good (rowAt 280) := by
  rw [row_280]
  unfold Good
  decide +kernel

theorem entry_281_checked : entryAt 281 = entry_281 := by
  rw [entry_chunk_13 15 (by decide)]
  decide +kernel
theorem row_281 : rowAt 281 = data_281 := by
  rw [rowAt, dif_neg (by decide : ¬ 281 < 6), entry_281_checked]
  change forkRow [placeRow ⟨36, 4, 5, 4⟩ (rowAt 36), placeRow ⟨163, 2, 5, 4⟩ (rowAt 163), placeRow ⟨189, 0, 4, 5⟩ (rowAt 189)] = data_281
  rw [row_36, row_163, row_189]
  apply row_ext <;> decide +kernel
theorem entry_good_281 : EntryGood 281 := by
  unfold EntryGood
  rw [entry_281_checked]
  decide +kernel
theorem good_281 : Good (rowAt 281) := by
  rw [row_281]
  unfold Good
  decide +kernel

theorem entry_282_checked : entryAt 282 = entry_282 := by
  rw [entry_chunk_13 16 (by decide)]
  decide +kernel
theorem row_282 : rowAt 282 = data_282 := by
  rw [rowAt, dif_neg (by decide : ¬ 282 < 6), entry_282_checked]
  change forkRow [placeRow ⟨56, 0, 5, 4⟩ (rowAt 56), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨265, 0, 1, 3⟩ (rowAt 265)] = data_282
  rw [row_56, row_64, row_55, row_265]
  apply row_ext <;> decide +kernel
theorem entry_good_282 : EntryGood 282 := by
  unfold EntryGood
  rw [entry_282_checked]
  decide +kernel
theorem good_282 : Good (rowAt 282) := by
  rw [row_282]
  unfold Good
  decide +kernel

theorem entry_283_checked : entryAt 283 = entry_283 := by
  rw [entry_chunk_13 17 (by decide)]
  decide +kernel
theorem row_283 : rowAt 283 = data_283 := by
  rw [rowAt, dif_neg (by decide : ¬ 283 < 6), entry_283_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨196, 1, 4, 3⟩ (rowAt 196), placeRow ⟨55, 2, 5, 4⟩ (rowAt 55)] = data_283
  rw [row_64, row_196, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_283 : EntryGood 283 := by
  unfold EntryGood
  rw [entry_283_checked]
  decide +kernel
theorem good_283 : Good (rowAt 283) := by
  rw [row_283]
  unfold Good
  decide +kernel


theorem block08_group03_piece00_correct : (rowAt 280 = data_280 ∧ Good (rowAt 280) ∧ EntryGood 280) ∧ (rowAt 281 = data_281 ∧ Good (rowAt 281) ∧ EntryGood 281) ∧ (rowAt 282 = data_282 ∧ Good (rowAt 282) ∧ EntryGood 282) ∧ (rowAt 283 = data_283 ∧ Good (rowAt 283) ∧ EntryGood 283) ∧ True := by
  exact ⟨⟨row_280, good_280, entry_good_280⟩, ⟨row_281, good_281, entry_good_281⟩, ⟨row_282, good_282, entry_good_282⟩, ⟨row_283, good_283, entry_good_283⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
