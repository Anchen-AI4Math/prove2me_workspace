import Definitions.Def_Snaky35Cache11
import Solutions.SnakyMilestones.Certificate35Part10
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_352_checked : entryAt 352 = entry_352 := by
  rw [entry_chunk_17 6 (by decide)]
  decide +kernel
theorem row_352 : rowAt 352 = data_352 := by
  rw [rowAt, dif_neg (by decide : ¬ 352 < 6), entry_352_checked]
  change forkRow [placeRow ⟨214, 0, 4, 5⟩ (rowAt 214), placeRow ⟨91, 0, 3, 4⟩ (rowAt 91), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨344, 0, 4, 5⟩ (rowAt 344), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180)] = data_352
  rw [row_214, row_91, row_63, row_344, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_352 : EntryGood 352 := by
  unfold EntryGood
  rw [entry_352_checked]
  decide +kernel
theorem good_352 : Good (rowAt 352) := by
  rw [row_352]
  unfold Good
  decide +kernel

theorem entry_353_checked : entryAt 353 = entry_353 := by
  rw [entry_chunk_17 7 (by decide)]
  decide +kernel
theorem row_353 : rowAt 353 = data_353 := by
  rw [rowAt, dif_neg (by decide : ¬ 353 < 6), entry_353_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨347, 0, 1, 3⟩ (rowAt 347)] = data_353
  rw [row_6, row_347]
  apply row_ext <;> decide +kernel
theorem entry_good_353 : EntryGood 353 := by
  unfold EntryGood
  rw [entry_353_checked]
  decide +kernel
theorem good_353 : Good (rowAt 353) := by
  rw [row_353]
  unfold Good
  decide +kernel

theorem entry_354_checked : entryAt 354 = entry_354 := by
  rw [entry_chunk_17 8 (by decide)]
  decide +kernel
theorem row_354 : rowAt 354 = data_354 := by
  rw [rowAt, dif_neg (by decide : ¬ 354 < 6), entry_354_checked]
  change forkRow [placeRow ⟨138, 2, 5, 4⟩ (rowAt 138), placeRow ⟨114, 5, 4, 3⟩ (rowAt 114), placeRow ⟨312, 0, 5, 5⟩ (rowAt 312), placeRow ⟨182, 2, 2, 4⟩ (rowAt 182)] = data_354
  rw [row_138, row_114, row_312, row_182]
  apply row_ext <;> decide +kernel
theorem entry_good_354 : EntryGood 354 := by
  unfold EntryGood
  rw [entry_354_checked]
  decide +kernel
theorem good_354 : Good (rowAt 354) := by
  rw [row_354]
  unfold Good
  decide +kernel

theorem entry_355_checked : entryAt 355 = entry_355 := by
  rw [entry_chunk_17 9 (by decide)]
  decide +kernel
theorem row_355 : rowAt 355 = data_355 := by
  rw [rowAt, dif_neg (by decide : ¬ 355 < 6), entry_355_checked]
  change forkRow [placeRow ⟨12, 2, 7, 3⟩ (rowAt 12), placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨342, 0, 6, 6⟩ (rowAt 342)] = data_355
  rw [row_12, row_167, row_342]
  apply row_ext <;> decide +kernel
theorem entry_good_355 : EntryGood 355 := by
  unfold EntryGood
  rw [entry_355_checked]
  decide +kernel
theorem good_355 : Good (rowAt 355) := by
  rw [row_355]
  unfold Good
  decide +kernel


theorem block11_group00_piece00_correct : (rowAt 352 = data_352 ∧ Good (rowAt 352) ∧ EntryGood 352) ∧ (rowAt 353 = data_353 ∧ Good (rowAt 353) ∧ EntryGood 353) ∧ (rowAt 354 = data_354 ∧ Good (rowAt 354) ∧ EntryGood 354) ∧ (rowAt 355 = data_355 ∧ Good (rowAt 355) ∧ EntryGood 355) ∧ True := by
  exact ⟨⟨row_352, good_352, entry_good_352⟩, ⟨row_353, good_353, entry_good_353⟩, ⟨row_354, good_354, entry_good_354⟩, ⟨row_355, good_355, entry_good_355⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
