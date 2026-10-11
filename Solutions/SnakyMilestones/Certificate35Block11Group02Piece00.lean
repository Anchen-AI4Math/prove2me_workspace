import Definitions.Def_Snaky35Cache11
import Solutions.SnakyMilestones.Certificate35Block11Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_368_checked : entryAt 368 = entry_368 := by
  rw [entry_chunk_18 2 (by decide)]
  decide +kernel
theorem row_368 : rowAt 368 = data_368 := by
  rw [rowAt, dif_neg (by decide : ¬ 368 < 6), entry_368_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨366, 0, 2, 4⟩ (rowAt 366)] = data_368
  rw [row_6, row_366]
  apply row_ext <;> decide +kernel
theorem entry_good_368 : EntryGood 368 := by
  unfold EntryGood
  rw [entry_368_checked]
  decide +kernel
theorem good_368 : Good (rowAt 368) := by
  rw [row_368]
  unfold Good
  decide +kernel

theorem entry_369_checked : entryAt 369 = entry_369 := by
  rw [entry_chunk_18 3 (by decide)]
  decide +kernel
theorem row_369 : rowAt 369 = data_369 := by
  rw [rowAt, dif_neg (by decide : ¬ 369 < 6), entry_369_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨367, 4, 1, 2⟩ (rowAt 367)] = data_369
  rw [row_6, row_367]
  apply row_ext <;> decide +kernel
theorem entry_good_369 : EntryGood 369 := by
  unfold EntryGood
  rw [entry_369_checked]
  decide +kernel
theorem good_369 : Good (rowAt 369) := by
  rw [row_369]
  unfold Good
  decide +kernel

theorem entry_370_checked : entryAt 370 = entry_370 := by
  rw [entry_chunk_18 4 (by decide)]
  decide +kernel
theorem row_370 : rowAt 370 = data_370 := by
  rw [rowAt, dif_neg (by decide : ¬ 370 < 6), entry_370_checked]
  change forkRow [placeRow ⟨199, 3, 1, 4⟩ (rowAt 199), placeRow ⟨286, 1, 5, 4⟩ (rowAt 286), placeRow ⟨24, 6, 1, 3⟩ (rowAt 24), placeRow ⟨319, 0, 5, 3⟩ (rowAt 319)] = data_370
  rw [row_199, row_286, row_24, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_370 : EntryGood 370 := by
  unfold EntryGood
  rw [entry_370_checked]
  decide +kernel
theorem good_370 : Good (rowAt 370) := by
  rw [row_370]
  unfold Good
  decide +kernel

theorem entry_371_checked : entryAt 371 = entry_371 := by
  rw [entry_chunk_18 5 (by decide)]
  decide +kernel
theorem row_371 : rowAt 371 = data_371 := by
  rw [rowAt, dif_neg (by decide : ¬ 371 < 6), entry_371_checked]
  change forkRow [placeRow ⟨267, 6, 2, 4⟩ (rowAt 267), placeRow ⟨137, 1, 4, 2⟩ (rowAt 137)] = data_371
  rw [row_267, row_137]
  apply row_ext <;> decide +kernel
theorem entry_good_371 : EntryGood 371 := by
  unfold EntryGood
  rw [entry_371_checked]
  decide +kernel
theorem good_371 : Good (rowAt 371) := by
  rw [row_371]
  unfold Good
  decide +kernel


theorem block11_group02_piece00_correct : (rowAt 368 = data_368 ∧ Good (rowAt 368) ∧ EntryGood 368) ∧ (rowAt 369 = data_369 ∧ Good (rowAt 369) ∧ EntryGood 369) ∧ (rowAt 370 = data_370 ∧ Good (rowAt 370) ∧ EntryGood 370) ∧ (rowAt 371 = data_371 ∧ Good (rowAt 371) ∧ EntryGood 371) ∧ True := by
  exact ⟨⟨row_368, good_368, entry_good_368⟩, ⟨row_369, good_369, entry_good_369⟩, ⟨row_370, good_370, entry_good_370⟩, ⟨row_371, good_371, entry_good_371⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
