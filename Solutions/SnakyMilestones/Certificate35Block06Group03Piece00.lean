import Definitions.Def_Snaky35Cache06
import Solutions.SnakyMilestones.Certificate35Block06Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_216_checked : entryAt 216 = entry_216 := by
  rw [entry_chunk_10 10 (by decide)]
  decide +kernel
theorem row_216 : rowAt 216 = data_216 := by
  rw [rowAt, dif_neg (by decide : ¬ 216 < 6), entry_216_checked]
  change forkRow [placeRow ⟨7, 6, 0, 3⟩ (rowAt 7), placeRow ⟨155, 5, 5, 4⟩ (rowAt 155)] = data_216
  rw [row_7, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_216 : EntryGood 216 := by
  unfold EntryGood
  rw [entry_216_checked]
  decide +kernel
theorem good_216 : Good (rowAt 216) := by
  rw [row_216]
  unfold Good
  decide +kernel

theorem entry_217_checked : entryAt 217 = entry_217 := by
  rw [entry_chunk_10 11 (by decide)]
  decide +kernel
theorem row_217 : rowAt 217 = data_217 := by
  rw [rowAt, dif_neg (by decide : ¬ 217 < 6), entry_217_checked]
  change forkRow [placeRow ⟨111, 1, 1, 3⟩ (rowAt 111), placeRow ⟨55, 4, 0, 4⟩ (rowAt 55), placeRow ⟨64, 0, 1, 3⟩ (rowAt 64)] = data_217
  rw [row_111, row_55, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_217 : EntryGood 217 := by
  unfold EntryGood
  rw [entry_217_checked]
  decide +kernel
theorem good_217 : Good (rowAt 217) := by
  rw [row_217]
  unfold Good
  decide +kernel

theorem entry_218_checked : entryAt 218 = entry_218 := by
  rw [entry_chunk_10 12 (by decide)]
  decide +kernel
theorem row_218 : rowAt 218 = data_218 := by
  rw [rowAt, dif_neg (by decide : ¬ 218 < 6), entry_218_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨182, 0, 2, 4⟩ (rowAt 182)] = data_218
  rw [row_0, row_182]
  apply row_ext <;> decide +kernel
theorem entry_good_218 : EntryGood 218 := by
  unfold EntryGood
  rw [entry_218_checked]
  decide +kernel
theorem good_218 : Good (rowAt 218) := by
  rw [row_218]
  unfold Good
  decide +kernel

theorem entry_219_checked : entryAt 219 = entry_219 := by
  rw [entry_chunk_10 13 (by decide)]
  decide +kernel
theorem row_219 : rowAt 219 = data_219 := by
  rw [rowAt, dif_neg (by decide : ¬ 219 < 6), entry_219_checked]
  change forkRow [placeRow ⟨0, 5, 3, 7⟩ (rowAt 0), placeRow ⟨179, 2, 6, 4⟩ (rowAt 179)] = data_219
  rw [row_0, row_179]
  apply row_ext <;> decide +kernel
theorem entry_good_219 : EntryGood 219 := by
  unfold EntryGood
  rw [entry_219_checked]
  decide +kernel
theorem good_219 : Good (rowAt 219) := by
  rw [row_219]
  unfold Good
  decide +kernel


theorem block06_group03_piece00_correct : (rowAt 216 = data_216 ∧ Good (rowAt 216) ∧ EntryGood 216) ∧ (rowAt 217 = data_217 ∧ Good (rowAt 217) ∧ EntryGood 217) ∧ (rowAt 218 = data_218 ∧ Good (rowAt 218) ∧ EntryGood 218) ∧ (rowAt 219 = data_219 ∧ Good (rowAt 219) ∧ EntryGood 219) ∧ True := by
  exact ⟨⟨row_216, good_216, entry_good_216⟩, ⟨row_217, good_217, entry_good_217⟩, ⟨row_218, good_218, entry_good_218⟩, ⟨row_219, good_219, entry_good_219⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
