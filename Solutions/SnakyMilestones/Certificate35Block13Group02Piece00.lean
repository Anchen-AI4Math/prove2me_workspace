import Definitions.Def_Snaky35Cache13
import Solutions.SnakyMilestones.Certificate35Block13Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_432_checked : entryAt 432 = entry_432 := by
  rw [entry_chunk_21 6 (by decide)]
  decide +kernel
theorem row_432 : rowAt 432 = data_432 := by
  rw [rowAt, dif_neg (by decide : ¬ 432 < 6), entry_432_checked]
  change forkRow [placeRow ⟨42, 3, 4, 3⟩ (rowAt 42), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨274, 0, 4, 3⟩ (rowAt 274)] = data_432
  rw [row_42, row_428, row_274]
  apply row_ext <;> decide +kernel
theorem entry_good_432 : EntryGood 432 := by
  unfold EntryGood
  rw [entry_432_checked]
  decide +kernel
theorem good_432 : Good (rowAt 432) := by
  rw [row_432]
  unfold Good
  decide +kernel

theorem entry_433_checked : entryAt 433 = entry_433 := by
  rw [entry_chunk_21 7 (by decide)]
  decide +kernel
theorem row_433 : rowAt 433 = data_433 := by
  rw [rowAt, dif_neg (by decide : ¬ 433 < 6), entry_433_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_433
  rw [row_63, row_7, row_427, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_433 : EntryGood 433 := by
  unfold EntryGood
  rw [entry_433_checked]
  decide +kernel
theorem good_433 : Good (rowAt 433) := by
  rw [row_433]
  unfold Good
  decide +kernel

theorem entry_434_checked : entryAt 434 = entry_434 := by
  rw [entry_chunk_21 8 (by decide)]
  decide +kernel
theorem row_434 : rowAt 434 = data_434 := by
  rw [rowAt, dif_neg (by decide : ¬ 434 < 6), entry_434_checked]
  change forkRow [placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨116, 0, 4, 3⟩ (rowAt 116)] = data_434
  rw [row_418, row_263, row_295, row_176, row_116]
  apply row_ext <;> decide +kernel
theorem entry_good_434 : EntryGood 434 := by
  unfold EntryGood
  rw [entry_434_checked]
  decide +kernel
theorem good_434 : Good (rowAt 434) := by
  rw [row_434]
  unfold Good
  decide +kernel

theorem entry_435_checked : entryAt 435 = entry_435 := by
  rw [entry_chunk_21 9 (by decide)]
  decide +kernel
theorem row_435 : rowAt 435 = data_435 := by
  rw [rowAt, dif_neg (by decide : ¬ 435 < 6), entry_435_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨431, 0, 5, 6⟩ (rowAt 431)] = data_435
  rw [row_6, row_431]
  apply row_ext <;> decide +kernel
theorem entry_good_435 : EntryGood 435 := by
  unfold EntryGood
  rw [entry_435_checked]
  decide +kernel
theorem good_435 : Good (rowAt 435) := by
  rw [row_435]
  unfold Good
  decide +kernel


theorem block13_group02_piece00_correct : (rowAt 432 = data_432 ∧ Good (rowAt 432) ∧ EntryGood 432) ∧ (rowAt 433 = data_433 ∧ Good (rowAt 433) ∧ EntryGood 433) ∧ (rowAt 434 = data_434 ∧ Good (rowAt 434) ∧ EntryGood 434) ∧ (rowAt 435 = data_435 ∧ Good (rowAt 435) ∧ EntryGood 435) ∧ True := by
  exact ⟨⟨row_432, good_432, entry_good_432⟩, ⟨row_433, good_433, entry_good_433⟩, ⟨row_434, good_434, entry_good_434⟩, ⟨row_435, good_435, entry_good_435⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
