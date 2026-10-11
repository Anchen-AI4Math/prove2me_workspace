import Definitions.Def_Snaky35Cache18
import Solutions.SnakyMilestones.Certificate35Block18Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_587_checked : entryAt 587 = entry_587 := by
  rw [entry_chunk_29 1 (by decide)]
  decide +kernel
theorem row_587 : rowAt 587 = data_587 := by
  rw [rowAt, dif_neg (by decide : ¬ 587 < 6), entry_587_checked]
  change forkRow [placeRow ⟨300, 2, 4, 1⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨319, 3, 5, 5⟩ (rowAt 319), placeRow ⟨477, 6, 4, 1⟩ (rowAt 477), placeRow ⟨252, 3, 4, 5⟩ (rowAt 252), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467)] = data_587
  rw [row_300, row_479, row_319, row_477, row_252, row_467]
  apply row_ext <;> decide +kernel
theorem entry_good_587 : EntryGood 587 := by
  unfold EntryGood
  rw [entry_587_checked]
  decide +kernel
theorem good_587 : Good (rowAt 587) := by
  rw [row_587]
  unfold Good
  decide +kernel

theorem entry_588_checked : entryAt 588 = entry_588 := by
  rw [entry_chunk_29 2 (by decide)]
  decide +kernel
theorem row_588 : rowAt 588 = data_588 := by
  rw [rowAt, dif_neg (by decide : ¬ 588 < 6), entry_588_checked]
  change forkRow [placeRow ⟨3, 1, 3, 3⟩ (rowAt 3), placeRow ⟨586, 0, 4, 5⟩ (rowAt 586)] = data_588
  rw [row_3, row_586]
  apply row_ext <;> decide +kernel
theorem entry_good_588 : EntryGood 588 := by
  unfold EntryGood
  rw [entry_588_checked]
  decide +kernel
theorem good_588 : Good (rowAt 588) := by
  rw [row_588]
  unfold Good
  decide +kernel

theorem block18_group02_correct : (rowAt 587 = data_587 ∧ Good (rowAt 587) ∧ EntryGood 587) ∧ (rowAt 588 = data_588 ∧ Good (rowAt 588) ∧ EntryGood 588) ∧ True := by
  exact ⟨⟨row_587, good_587, entry_good_587⟩, ⟨row_588, good_588, entry_good_588⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
