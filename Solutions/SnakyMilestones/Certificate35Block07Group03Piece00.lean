import Definitions.Def_Snaky35Cache07
import Solutions.SnakyMilestones.Certificate35Block07Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_248_checked : entryAt 248 = entry_248 := by
  rw [entry_chunk_12 2 (by decide)]
  decide +kernel
theorem row_248 : rowAt 248 = data_248 := by
  rw [rowAt, dif_neg (by decide : ¬ 248 < 6), entry_248_checked]
  change forkRow [placeRow ⟨186, 0, 7, 4⟩ (rowAt 186), placeRow ⟨143, 0, 3, 3⟩ (rowAt 143), placeRow ⟨175, 2, 7, 4⟩ (rowAt 175), placeRow ⟨64, 6, 6, 5⟩ (rowAt 64)] = data_248
  rw [row_186, row_143, row_175, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_248 : EntryGood 248 := by
  unfold EntryGood
  rw [entry_248_checked]
  decide +kernel
theorem good_248 : Good (rowAt 248) := by
  rw [row_248]
  unfold Good
  decide +kernel

theorem entry_249_checked : entryAt 249 = entry_249 := by
  rw [entry_chunk_12 3 (by decide)]
  decide +kernel
theorem row_249 : rowAt 249 = data_249 := by
  rw [rowAt, dif_neg (by decide : ¬ 249 < 6), entry_249_checked]
  change forkRow [placeRow ⟨0, 7, 4, 5⟩ (rowAt 0), placeRow ⟨225, 1, 4, 1⟩ (rowAt 225)] = data_249
  rw [row_0, row_225]
  apply row_ext <;> decide +kernel
theorem entry_good_249 : EntryGood 249 := by
  unfold EntryGood
  rw [entry_249_checked]
  decide +kernel
theorem good_249 : Good (rowAt 249) := by
  rw [row_249]
  unfold Good
  decide +kernel

theorem entry_250_checked : entryAt 250 = entry_250 := by
  rw [entry_chunk_12 4 (by decide)]
  decide +kernel
theorem row_250 : rowAt 250 = data_250 := by
  rw [rowAt, dif_neg (by decide : ¬ 250 < 6), entry_250_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨238, 0, 2, 4⟩ (rowAt 238)] = data_250
  rw [row_6, row_238]
  apply row_ext <;> decide +kernel
theorem entry_good_250 : EntryGood 250 := by
  unfold EntryGood
  rw [entry_250_checked]
  decide +kernel
theorem good_250 : Good (rowAt 250) := by
  rw [row_250]
  unfold Good
  decide +kernel

theorem entry_251_checked : entryAt 251 = entry_251 := by
  rw [entry_chunk_12 5 (by decide)]
  decide +kernel
theorem row_251 : rowAt 251 = data_251 := by
  rw [rowAt, dif_neg (by decide : ¬ 251 < 6), entry_251_checked]
  change forkRow [placeRow ⟨6, 2, 5, 4⟩ (rowAt 6), placeRow ⟨239, 4, 3, 6⟩ (rowAt 239)] = data_251
  rw [row_6, row_239]
  apply row_ext <;> decide +kernel
theorem entry_good_251 : EntryGood 251 := by
  unfold EntryGood
  rw [entry_251_checked]
  decide +kernel
theorem good_251 : Good (rowAt 251) := by
  rw [row_251]
  unfold Good
  decide +kernel


theorem block07_group03_piece00_correct : (rowAt 248 = data_248 ∧ Good (rowAt 248) ∧ EntryGood 248) ∧ (rowAt 249 = data_249 ∧ Good (rowAt 249) ∧ EntryGood 249) ∧ (rowAt 250 = data_250 ∧ Good (rowAt 250) ∧ EntryGood 250) ∧ (rowAt 251 = data_251 ∧ Good (rowAt 251) ∧ EntryGood 251) ∧ True := by
  exact ⟨⟨row_248, good_248, entry_good_248⟩, ⟨row_249, good_249, entry_good_249⟩, ⟨row_250, good_250, entry_good_250⟩, ⟨row_251, good_251, entry_good_251⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
