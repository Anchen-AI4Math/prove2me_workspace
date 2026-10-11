import Definitions.Def_Snaky35Cache14
import Solutions.SnakyMilestones.Certificate35Part13
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_448_checked : entryAt 448 = entry_448 := by
  rw [entry_chunk_22 2 (by decide)]
  decide +kernel
theorem row_448 : rowAt 448 = data_448 := by
  rw [rowAt, dif_neg (by decide : ¬ 448 < 6), entry_448_checked]
  change forkRow [placeRow ⟨9, 4, 1, 3⟩ (rowAt 9), placeRow ⟨436, 0, 3, 6⟩ (rowAt 436)] = data_448
  rw [row_9, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_448 : EntryGood 448 := by
  unfold EntryGood
  rw [entry_448_checked]
  decide +kernel
theorem good_448 : Good (rowAt 448) := by
  rw [row_448]
  unfold Good
  decide +kernel

theorem entry_449_checked : entryAt 449 = entry_449 := by
  rw [entry_chunk_22 3 (by decide)]
  decide +kernel
theorem row_449 : rowAt 449 = data_449 := by
  rw [rowAt, dif_neg (by decide : ¬ 449 < 6), entry_449_checked]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨439, 0, 5, 4⟩ (rowAt 439), placeRow ⟨307, 0, 4, 3⟩ (rowAt 307)] = data_449
  rw [row_26, row_244, row_439, row_307]
  apply row_ext <;> decide +kernel
theorem entry_good_449 : EntryGood 449 := by
  unfold EntryGood
  rw [entry_449_checked]
  decide +kernel
theorem good_449 : Good (rowAt 449) := by
  rw [row_449]
  unfold Good
  decide +kernel

theorem entry_450_checked : entryAt 450 = entry_450 := by
  rw [entry_chunk_22 4 (by decide)]
  decide +kernel
theorem row_450 : rowAt 450 = data_450 := by
  rw [rowAt, dif_neg (by decide : ¬ 450 < 6), entry_450_checked]
  change forkRow [placeRow ⟨6, 1, 5, 5⟩ (rowAt 6), placeRow ⟨440, 0, 6, 4⟩ (rowAt 440)] = data_450
  rw [row_6, row_440]
  apply row_ext <;> decide +kernel
theorem entry_good_450 : EntryGood 450 := by
  unfold EntryGood
  rw [entry_450_checked]
  decide +kernel
theorem good_450 : Good (rowAt 450) := by
  rw [row_450]
  unfold Good
  decide +kernel

theorem entry_451_checked : entryAt 451 = entry_451 := by
  rw [entry_chunk_22 5 (by decide)]
  decide +kernel
theorem row_451 : rowAt 451 = data_451 := by
  rw [rowAt, dif_neg (by decide : ¬ 451 < 6), entry_451_checked]
  change forkRow [placeRow ⟨1, 5, 4, 3⟩ (rowAt 1), placeRow ⟨449, 0, 5, 4⟩ (rowAt 449)] = data_451
  rw [row_1, row_449]
  apply row_ext <;> decide +kernel
theorem entry_good_451 : EntryGood 451 := by
  unfold EntryGood
  rw [entry_451_checked]
  decide +kernel
theorem good_451 : Good (rowAt 451) := by
  rw [row_451]
  unfold Good
  decide +kernel


theorem block14_group00_piece00_correct : (rowAt 448 = data_448 ∧ Good (rowAt 448) ∧ EntryGood 448) ∧ (rowAt 449 = data_449 ∧ Good (rowAt 449) ∧ EntryGood 449) ∧ (rowAt 450 = data_450 ∧ Good (rowAt 450) ∧ EntryGood 450) ∧ (rowAt 451 = data_451 ∧ Good (rowAt 451) ∧ EntryGood 451) ∧ True := by
  exact ⟨⟨row_448, good_448, entry_good_448⟩, ⟨row_449, good_449, entry_good_449⟩, ⟨row_450, good_450, entry_good_450⟩, ⟨row_451, good_451, entry_good_451⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
