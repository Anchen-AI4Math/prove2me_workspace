import Definitions.Def_Snaky35Cache17
import Solutions.SnakyMilestones.Certificate35Block17Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_560_checked : entryAt 560 = entry_560 := by
  rw [entry_chunk_27 14 (by decide)]
  decide +kernel
theorem row_560 : rowAt 560 = data_560 := by
  rw [rowAt, dif_neg (by decide : ¬ 560 < 6), entry_560_checked]
  change forkRow [placeRow ⟨517, 5, 5, 4⟩ (rowAt 517), placeRow ⟨416, 5, 4, 3⟩ (rowAt 416), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359), placeRow ⟨356, 6, 3, 4⟩ (rowAt 356), placeRow ⟨483, 0, 4, 6⟩ (rowAt 483)] = data_560
  rw [row_517, row_416, row_359, row_356, row_483]
  apply row_ext <;> decide +kernel
theorem entry_good_560 : EntryGood 560 := by
  unfold EntryGood
  rw [entry_560_checked]
  decide +kernel
theorem good_560 : Good (rowAt 560) := by
  rw [row_560]
  unfold Good
  decide +kernel

theorem entry_561_checked : entryAt 561 = entry_561 := by
  rw [entry_chunk_27 15 (by decide)]
  decide +kernel
theorem row_561 : rowAt 561 = data_561 := by
  rw [rowAt, dif_neg (by decide : ¬ 561 < 6), entry_561_checked]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨263, 6, 1, 4⟩ (rowAt 263), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨546, 4, 5, 4⟩ (rowAt 546), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨535, 0, 4, 5⟩ (rowAt 535)] = data_561
  rw [row_295, row_173, row_263, row_236, row_546, row_176, row_535]
  apply row_ext <;> decide +kernel
theorem entry_good_561 : EntryGood 561 := by
  unfold EntryGood
  rw [entry_561_checked]
  decide +kernel
theorem good_561 : Good (rowAt 561) := by
  rw [row_561]
  unfold Good
  decide +kernel

theorem entry_562_checked : entryAt 562 = entry_562 := by
  rw [entry_chunk_27 16 (by decide)]
  decide +kernel
theorem row_562 : rowAt 562 = data_562 := by
  rw [rowAt, dif_neg (by decide : ¬ 562 < 6), entry_562_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨559, 0, 4, 5⟩ (rowAt 559)] = data_562
  rw [row_6, row_559]
  apply row_ext <;> decide +kernel
theorem entry_good_562 : EntryGood 562 := by
  unfold EntryGood
  rw [entry_562_checked]
  decide +kernel
theorem good_562 : Good (rowAt 562) := by
  rw [row_562]
  unfold Good
  decide +kernel

theorem entry_563_checked : entryAt 563 = entry_563 := by
  rw [entry_chunk_27 17 (by decide)]
  decide +kernel
theorem row_563 : rowAt 563 = data_563 := by
  rw [rowAt, dif_neg (by decide : ¬ 563 < 6), entry_563_checked]
  change forkRow [placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514), placeRow ⟨330, 4, 3, 4⟩ (rowAt 330), placeRow ⟨545, 0, 5, 5⟩ (rowAt 545)] = data_563
  rw [row_167, row_538, row_514, row_330, row_545]
  apply row_ext <;> decide +kernel
theorem entry_good_563 : EntryGood 563 := by
  unfold EntryGood
  rw [entry_563_checked]
  decide +kernel
theorem good_563 : Good (rowAt 563) := by
  rw [row_563]
  unfold Good
  decide +kernel


theorem block17_group02_piece00_correct : (rowAt 560 = data_560 ∧ Good (rowAt 560) ∧ EntryGood 560) ∧ (rowAt 561 = data_561 ∧ Good (rowAt 561) ∧ EntryGood 561) ∧ (rowAt 562 = data_562 ∧ Good (rowAt 562) ∧ EntryGood 562) ∧ (rowAt 563 = data_563 ∧ Good (rowAt 563) ∧ EntryGood 563) ∧ True := by
  exact ⟨⟨row_560, good_560, entry_good_560⟩, ⟨row_561, good_561, entry_good_561⟩, ⟨row_562, good_562, entry_good_562⟩, ⟨row_563, good_563, entry_good_563⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
