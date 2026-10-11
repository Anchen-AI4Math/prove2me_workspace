import Definitions.Def_Snaky35Cache10
import Solutions.SnakyMilestones.Certificate35Block10Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_344_checked : entryAt 344 = entry_344 := by
  rw [entry_chunk_16 18 (by decide)]
  decide +kernel
theorem row_344 : rowAt 344 = data_344 := by
  rw [rowAt, dif_neg (by decide : ¬ 344 < 6), entry_344_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨108, 3, 4, 5⟩ (rowAt 108), placeRow ⟨262, 4, 5, 2⟩ (rowAt 262)] = data_344
  rw [row_7, row_108, row_262]
  apply row_ext <;> decide +kernel
theorem entry_good_344 : EntryGood 344 := by
  unfold EntryGood
  rw [entry_344_checked]
  decide +kernel
theorem good_344 : Good (rowAt 344) := by
  rw [row_344]
  unfold Good
  decide +kernel

theorem entry_345_checked : entryAt 345 = entry_345 := by
  rw [entry_chunk_16 19 (by decide)]
  decide +kernel
theorem row_345 : rowAt 345 = data_345 := by
  rw [rowAt, dif_neg (by decide : ¬ 345 < 6), entry_345_checked]
  change forkRow [placeRow ⟨6, 0, 5, 5⟩ (rowAt 6), placeRow ⟨320, 4, 4, 7⟩ (rowAt 320)] = data_345
  rw [row_6, row_320]
  apply row_ext <;> decide +kernel
theorem entry_good_345 : EntryGood 345 := by
  unfold EntryGood
  rw [entry_345_checked]
  decide +kernel
theorem good_345 : Good (rowAt 345) := by
  rw [row_345]
  unfold Good
  decide +kernel

theorem entry_346_checked : entryAt 346 = entry_346 := by
  rw [entry_chunk_17 0 (by decide)]
  decide +kernel
theorem row_346 : rowAt 346 = data_346 := by
  rw [rowAt, dif_neg (by decide : ¬ 346 < 6), entry_346_checked]
  change forkRow [placeRow ⟨60, 1, 4, 3⟩ (rowAt 60), placeRow ⟨255, 0, 1, 4⟩ (rowAt 255), placeRow ⟨276, 0, 1, 4⟩ (rowAt 276)] = data_346
  rw [row_60, row_255, row_276]
  apply row_ext <;> decide +kernel
theorem entry_good_346 : EntryGood 346 := by
  unfold EntryGood
  rw [entry_346_checked]
  decide +kernel
theorem good_346 : Good (rowAt 346) := by
  rw [row_346]
  unfold Good
  decide +kernel

theorem entry_347_checked : entryAt 347 = entry_347 := by
  rw [entry_chunk_17 1 (by decide)]
  decide +kernel
theorem row_347 : rowAt 347 = data_347 := by
  rw [rowAt, dif_neg (by decide : ¬ 347 < 6), entry_347_checked]
  change forkRow [placeRow ⟨6, 6, 3, 4⟩ (rowAt 6), placeRow ⟨339, 0, 5, 8⟩ (rowAt 339)] = data_347
  rw [row_6, row_339]
  apply row_ext <;> decide +kernel
theorem entry_good_347 : EntryGood 347 := by
  unfold EntryGood
  rw [entry_347_checked]
  decide +kernel
theorem good_347 : Good (rowAt 347) := by
  rw [row_347]
  unfold Good
  decide +kernel


theorem block10_group03_piece00_correct : (rowAt 344 = data_344 ∧ Good (rowAt 344) ∧ EntryGood 344) ∧ (rowAt 345 = data_345 ∧ Good (rowAt 345) ∧ EntryGood 345) ∧ (rowAt 346 = data_346 ∧ Good (rowAt 346) ∧ EntryGood 346) ∧ (rowAt 347 = data_347 ∧ Good (rowAt 347) ∧ EntryGood 347) ∧ True := by
  exact ⟨⟨row_344, good_344, entry_good_344⟩, ⟨row_345, good_345, entry_good_345⟩, ⟨row_346, good_346, entry_good_346⟩, ⟨row_347, good_347, entry_good_347⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
