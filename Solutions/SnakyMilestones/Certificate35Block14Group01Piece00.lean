import Definitions.Def_Snaky35Cache14
import Solutions.SnakyMilestones.Certificate35Block14Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_456_checked : entryAt 456 = entry_456 := by
  rw [entry_chunk_22 10 (by decide)]
  decide +kernel
theorem row_456 : rowAt 456 = data_456 := by
  rw [rowAt, dif_neg (by decide : ¬ 456 < 6), entry_456_checked]
  change forkRow [placeRow ⟨308, 4, 4, 3⟩ (rowAt 308), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55)] = data_456
  rw [row_308, row_64, row_63, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_456 : EntryGood 456 := by
  unfold EntryGood
  rw [entry_456_checked]
  decide +kernel
theorem good_456 : Good (rowAt 456) := by
  rw [row_456]
  unfold Good
  decide +kernel

theorem entry_457_checked : entryAt 457 = entry_457 := by
  rw [entry_chunk_22 11 (by decide)]
  decide +kernel
theorem row_457 : rowAt 457 = data_457 := by
  rw [rowAt, dif_neg (by decide : ¬ 457 < 6), entry_457_checked]
  change forkRow [placeRow ⟨28, 7, 3, 2⟩ (rowAt 28), placeRow ⟨454, 0, 5, 4⟩ (rowAt 454)] = data_457
  rw [row_28, row_454]
  apply row_ext <;> decide +kernel
theorem entry_good_457 : EntryGood 457 := by
  unfold EntryGood
  rw [entry_457_checked]
  decide +kernel
theorem good_457 : Good (rowAt 457) := by
  rw [row_457]
  unfold Good
  decide +kernel

theorem entry_458_checked : entryAt 458 = entry_458 := by
  rw [entry_chunk_22 12 (by decide)]
  decide +kernel
theorem row_458 : rowAt 458 = data_458 := by
  rw [rowAt, dif_neg (by decide : ¬ 458 < 6), entry_458_checked]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨177, 1, 4, 2⟩ (rowAt 177), placeRow ⟨450, 0, 1, 4⟩ (rowAt 450)] = data_458
  rw [row_130, row_177, row_450]
  apply row_ext <;> decide +kernel
theorem entry_good_458 : EntryGood 458 := by
  unfold EntryGood
  rw [entry_458_checked]
  decide +kernel
theorem good_458 : Good (rowAt 458) := by
  rw [row_458]
  unfold Good
  decide +kernel

theorem entry_459_checked : entryAt 459 = entry_459 := by
  rw [entry_chunk_22 13 (by decide)]
  decide +kernel
theorem row_459 : rowAt 459 = data_459 := by
  rw [rowAt, dif_neg (by decide : ¬ 459 < 6), entry_459_checked]
  change forkRow [placeRow ⟨97, 2, 7, 3⟩ (rowAt 97), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨65, 2, 7, 3⟩ (rowAt 65)] = data_459
  rw [row_97, row_448, row_65]
  apply row_ext <;> decide +kernel
theorem entry_good_459 : EntryGood 459 := by
  unfold EntryGood
  rw [entry_459_checked]
  decide +kernel
theorem good_459 : Good (rowAt 459) := by
  rw [row_459]
  unfold Good
  decide +kernel


theorem block14_group01_piece00_correct : (rowAt 456 = data_456 ∧ Good (rowAt 456) ∧ EntryGood 456) ∧ (rowAt 457 = data_457 ∧ Good (rowAt 457) ∧ EntryGood 457) ∧ (rowAt 458 = data_458 ∧ Good (rowAt 458) ∧ EntryGood 458) ∧ (rowAt 459 = data_459 ∧ Good (rowAt 459) ∧ EntryGood 459) ∧ True := by
  exact ⟨⟨row_456, good_456, entry_good_456⟩, ⟨row_457, good_457, entry_good_457⟩, ⟨row_458, good_458, entry_good_458⟩, ⟨row_459, good_459, entry_good_459⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
