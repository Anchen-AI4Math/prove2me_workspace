import Definitions.Def_Snaky35Cache14
import Solutions.SnakyMilestones.Certificate35Block14Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_472_checked : entryAt 472 = entry_472 := by
  rw [entry_chunk_23 6 (by decide)]
  decide +kernel
theorem row_472 : rowAt 472 = data_472 := by
  rw [rowAt, dif_neg (by decide : ¬ 472 < 6), entry_472_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466)] = data_472
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_472 : EntryGood 472 := by
  unfold EntryGood
  rw [entry_472_checked]
  decide +kernel
theorem good_472 : Good (rowAt 472) := by
  rw [row_472]
  unfold Good
  decide +kernel

theorem entry_473_checked : entryAt 473 = entry_473 := by
  rw [entry_chunk_23 7 (by decide)]
  decide +kernel
theorem row_473 : rowAt 473 = data_473 := by
  rw [rowAt, dif_neg (by decide : ¬ 473 < 6), entry_473_checked]
  change forkRow [placeRow ⟨121, 5, 5, 4⟩ (rowAt 121), placeRow ⟨436, 0, 3, 7⟩ (rowAt 436), placeRow ⟨445, 4, 5, 4⟩ (rowAt 445)] = data_473
  rw [row_121, row_436, row_445]
  apply row_ext <;> decide +kernel
theorem entry_good_473 : EntryGood 473 := by
  unfold EntryGood
  rw [entry_473_checked]
  decide +kernel
theorem good_473 : Good (rowAt 473) := by
  rw [row_473]
  unfold Good
  decide +kernel

theorem entry_474_checked : entryAt 474 = entry_474 := by
  rw [entry_chunk_23 8 (by decide)]
  decide +kernel
theorem row_474 : rowAt 474 = data_474 := by
  rw [rowAt, dif_neg (by decide : ¬ 474 < 6), entry_474_checked]
  change forkRow [placeRow ⟨463, 0, 6, 5⟩ (rowAt 463), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70), placeRow ⟨83, 1, 5, 3⟩ (rowAt 83)] = data_474
  rw [row_463, row_70, row_83]
  apply row_ext <;> decide +kernel
theorem entry_good_474 : EntryGood 474 := by
  unfold EntryGood
  rw [entry_474_checked]
  decide +kernel
theorem good_474 : Good (rowAt 474) := by
  rw [row_474]
  unfold Good
  decide +kernel

theorem entry_475_checked : entryAt 475 = entry_475 := by
  rw [entry_chunk_23 9 (by decide)]
  decide +kernel
theorem row_475 : rowAt 475 = data_475 := by
  rw [rowAt, dif_neg (by decide : ¬ 475 < 6), entry_475_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨261, 1, 4, 3⟩ (rowAt 261), placeRow ⟨457, 0, 2, 5⟩ (rowAt 457), placeRow ⟨269, 2, 2, 5⟩ (rowAt 269)] = data_475
  rw [row_63, row_261, row_457, row_269]
  apply row_ext <;> decide +kernel
theorem entry_good_475 : EntryGood 475 := by
  unfold EntryGood
  rw [entry_475_checked]
  decide +kernel
theorem good_475 : Good (rowAt 475) := by
  rw [row_475]
  unfold Good
  decide +kernel


theorem block14_group03_piece00_correct : (rowAt 472 = data_472 ∧ Good (rowAt 472) ∧ EntryGood 472) ∧ (rowAt 473 = data_473 ∧ Good (rowAt 473) ∧ EntryGood 473) ∧ (rowAt 474 = data_474 ∧ Good (rowAt 474) ∧ EntryGood 474) ∧ (rowAt 475 = data_475 ∧ Good (rowAt 475) ∧ EntryGood 475) ∧ True := by
  exact ⟨⟨row_472, good_472, entry_good_472⟩, ⟨row_473, good_473, entry_good_473⟩, ⟨row_474, good_474, entry_good_474⟩, ⟨row_475, good_475, entry_good_475⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
