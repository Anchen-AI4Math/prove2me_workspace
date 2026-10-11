import Definitions.Def_Snaky35Cache17
import Solutions.SnakyMilestones.Certificate35Part16
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_544_checked : entryAt 544 = entry_544 := by
  rw [entry_chunk_26 18 (by decide)]
  decide +kernel
theorem row_544 : rowAt 544 = data_544 := by
  rw [rowAt, dif_neg (by decide : ¬ 544 < 6), entry_544_checked]
  change forkRow [placeRow ⟨263, 2, 7, 4⟩ (rowAt 263), placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨451, 1, 8, 3⟩ (rowAt 451)] = data_544
  rw [row_263, row_9, row_451]
  apply row_ext <;> decide +kernel
theorem entry_good_544 : EntryGood 544 := by
  unfold EntryGood
  rw [entry_544_checked]
  decide +kernel
theorem good_544 : Good (rowAt 544) := by
  rw [row_544]
  unfold Good
  decide +kernel

theorem entry_545_checked : entryAt 545 = entry_545 := by
  rw [entry_chunk_26 19 (by decide)]
  decide +kernel
theorem row_545 : rowAt 545 = data_545 := by
  rw [rowAt, dif_neg (by decide : ¬ 545 < 6), entry_545_checked]
  change forkRow [placeRow ⟨256, 0, 4, 5⟩ (rowAt 256), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨153, 0, 6, 3⟩ (rowAt 153), placeRow ⟨343, 0, 4, 5⟩ (rowAt 343)] = data_545
  rw [row_256, row_448, row_153, row_343]
  apply row_ext <;> decide +kernel
theorem entry_good_545 : EntryGood 545 := by
  unfold EntryGood
  rw [entry_545_checked]
  decide +kernel
theorem good_545 : Good (rowAt 545) := by
  rw [row_545]
  unfold Good
  decide +kernel

theorem entry_546_checked : entryAt 546 = entry_546 := by
  rw [entry_chunk_27 0 (by decide)]
  decide +kernel
theorem row_546 : rowAt 546 = data_546 := by
  rw [rowAt, dif_neg (by decide : ¬ 546 < 6), entry_546_checked]
  change forkRow [placeRow ⟨64, 0, 4, 3⟩ (rowAt 64), placeRow ⟨482, 7, 4, 3⟩ (rowAt 482), placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_546
  rw [row_64, row_482, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_546 : EntryGood 546 := by
  unfold EntryGood
  rw [entry_546_checked]
  decide +kernel
theorem good_546 : Good (rowAt 546) := by
  rw [row_546]
  unfold Good
  decide +kernel

theorem entry_547_checked : entryAt 547 = entry_547 := by
  rw [entry_chunk_27 1 (by decide)]
  decide +kernel
theorem row_547 : rowAt 547 = data_547 := by
  rw [rowAt, dif_neg (by decide : ¬ 547 < 6), entry_547_checked]
  change forkRow [placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨510, 4, 7, 5⟩ (rowAt 510), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131)] = data_547
  rw [row_443, row_510, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_547 : EntryGood 547 := by
  unfold EntryGood
  rw [entry_547_checked]
  decide +kernel
theorem good_547 : Good (rowAt 547) := by
  rw [row_547]
  unfold Good
  decide +kernel


theorem block17_group00_piece00_correct : (rowAt 544 = data_544 ∧ Good (rowAt 544) ∧ EntryGood 544) ∧ (rowAt 545 = data_545 ∧ Good (rowAt 545) ∧ EntryGood 545) ∧ (rowAt 546 = data_546 ∧ Good (rowAt 546) ∧ EntryGood 546) ∧ (rowAt 547 = data_547 ∧ Good (rowAt 547) ∧ EntryGood 547) ∧ True := by
  exact ⟨⟨row_544, good_544, entry_good_544⟩, ⟨row_545, good_545, entry_good_545⟩, ⟨row_546, good_546, entry_good_546⟩, ⟨row_547, good_547, entry_good_547⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
