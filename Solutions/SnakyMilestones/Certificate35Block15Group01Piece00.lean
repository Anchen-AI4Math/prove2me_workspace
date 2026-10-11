import Definitions.Def_Snaky35Cache15
import Solutions.SnakyMilestones.Certificate35Block15Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_488_checked : entryAt 488 = entry_488 := by
  rw [entry_chunk_24 2 (by decide)]
  decide +kernel
theorem row_488 : rowAt 488 = data_488 := by
  rw [rowAt, dif_neg (by decide : ¬ 488 < 6), entry_488_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨247, 0, 2, 5⟩ (rowAt 247)] = data_488
  rw [row_0, row_247]
  apply row_ext <;> decide +kernel
theorem entry_good_488 : EntryGood 488 := by
  unfold EntryGood
  rw [entry_488_checked]
  decide +kernel
theorem good_488 : Good (rowAt 488) := by
  rw [row_488]
  unfold Good
  decide +kernel

theorem entry_489_checked : entryAt 489 = entry_489 := by
  rw [entry_chunk_24 3 (by decide)]
  decide +kernel
theorem row_489 : rowAt 489 = data_489 := by
  rw [rowAt, dif_neg (by decide : ¬ 489 < 6), entry_489_checked]
  change forkRow [placeRow ⟨356, 1, 3, 3⟩ (rowAt 356), placeRow ⟨197, 4, 1, 4⟩ (rowAt 197), placeRow ⟨172, 6, 1, 4⟩ (rowAt 172)] = data_489
  rw [row_356, row_197, row_172]
  apply row_ext <;> decide +kernel
theorem entry_good_489 : EntryGood 489 := by
  unfold EntryGood
  rw [entry_489_checked]
  decide +kernel
theorem good_489 : Good (rowAt 489) := by
  rw [row_489]
  unfold Good
  decide +kernel

theorem entry_490_checked : entryAt 490 = entry_490 := by
  rw [entry_chunk_24 4 (by decide)]
  decide +kernel
theorem row_490 : rowAt 490 = data_490 := by
  rw [rowAt, dif_neg (by decide : ¬ 490 < 6), entry_490_checked]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨470, 1, 5, 1⟩ (rowAt 470), placeRow ⟨111, 0, 3, 1⟩ (rowAt 111)] = data_490
  rw [row_64, row_471, row_470, row_111]
  apply row_ext <;> decide +kernel
theorem entry_good_490 : EntryGood 490 := by
  unfold EntryGood
  rw [entry_490_checked]
  decide +kernel
theorem good_490 : Good (rowAt 490) := by
  rw [row_490]
  unfold Good
  decide +kernel

theorem entry_491_checked : entryAt 491 = entry_491 := by
  rw [entry_chunk_24 5 (by decide)]
  decide +kernel
theorem row_491 : rowAt 491 = data_491 := by
  rw [rowAt, dif_neg (by decide : ¬ 491 < 6), entry_491_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨273, 0, 5, 4⟩ (rowAt 273)] = data_491
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_491 : EntryGood 491 := by
  unfold EntryGood
  rw [entry_491_checked]
  decide +kernel
theorem good_491 : Good (rowAt 491) := by
  rw [row_491]
  unfold Good
  decide +kernel


theorem block15_group01_piece00_correct : (rowAt 488 = data_488 ∧ Good (rowAt 488) ∧ EntryGood 488) ∧ (rowAt 489 = data_489 ∧ Good (rowAt 489) ∧ EntryGood 489) ∧ (rowAt 490 = data_490 ∧ Good (rowAt 490) ∧ EntryGood 490) ∧ (rowAt 491 = data_491 ∧ Good (rowAt 491) ∧ EntryGood 491) ∧ True := by
  exact ⟨⟨row_488, good_488, entry_good_488⟩, ⟨row_489, good_489, entry_good_489⟩, ⟨row_490, good_490, entry_good_490⟩, ⟨row_491, good_491, entry_good_491⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
