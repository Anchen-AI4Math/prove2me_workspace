import Definitions.Def_Snaky35Cache09
import Solutions.SnakyMilestones.Certificate35Block09Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_312_checked : entryAt 312 = entry_312 := by
  rw [entry_chunk_15 6 (by decide)]
  decide +kernel
theorem row_312 : rowAt 312 = data_312 := by
  rw [rowAt, dif_neg (by decide : ¬ 312 < 6), entry_312_checked]
  change forkRow [placeRow ⟨9, 2, 5, 4⟩ (rowAt 9), placeRow ⟨272, 0, 4, 5⟩ (rowAt 272)] = data_312
  rw [row_9, row_272]
  apply row_ext <;> decide +kernel
theorem entry_good_312 : EntryGood 312 := by
  unfold EntryGood
  rw [entry_312_checked]
  decide +kernel
theorem good_312 : Good (rowAt 312) := by
  rw [row_312]
  unfold Good
  decide +kernel

theorem entry_313_checked : entryAt 313 = entry_313 := by
  rw [entry_chunk_15 7 (by decide)]
  decide +kernel
theorem row_313 : rowAt 313 = data_313 := by
  rw [rowAt, dif_neg (by decide : ¬ 313 < 6), entry_313_checked]
  change forkRow [placeRow ⟨162, 4, 4, 5⟩ (rowAt 162), placeRow ⟨148, 5, 6, 3⟩ (rowAt 148)] = data_313
  rw [row_162, row_148]
  apply row_ext <;> decide +kernel
theorem entry_good_313 : EntryGood 313 := by
  unfold EntryGood
  rw [entry_313_checked]
  decide +kernel
theorem good_313 : Good (rowAt 313) := by
  rw [row_313]
  unfold Good
  decide +kernel

theorem entry_314_checked : entryAt 314 = entry_314 := by
  rw [entry_chunk_15 8 (by decide)]
  decide +kernel
theorem row_314 : rowAt 314 = data_314 := by
  rw [rowAt, dif_neg (by decide : ¬ 314 < 6), entry_314_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨305, 0, 6, 4⟩ (rowAt 305)] = data_314
  rw [row_6, row_305]
  apply row_ext <;> decide +kernel
theorem entry_good_314 : EntryGood 314 := by
  unfold EntryGood
  rw [entry_314_checked]
  decide +kernel
theorem good_314 : Good (rowAt 314) := by
  rw [row_314]
  unfold Good
  decide +kernel

theorem entry_315_checked : entryAt 315 = entry_315 := by
  rw [entry_chunk_15 9 (by decide)]
  decide +kernel
theorem row_315 : rowAt 315 = data_315 := by
  rw [rowAt, dif_neg (by decide : ¬ 315 < 6), entry_315_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨296, 0, 4, 5⟩ (rowAt 296)] = data_315
  rw [row_6, row_296]
  apply row_ext <;> decide +kernel
theorem entry_good_315 : EntryGood 315 := by
  unfold EntryGood
  rw [entry_315_checked]
  decide +kernel
theorem good_315 : Good (rowAt 315) := by
  rw [row_315]
  unfold Good
  decide +kernel


theorem block09_group03_piece00_correct : (rowAt 312 = data_312 ∧ Good (rowAt 312) ∧ EntryGood 312) ∧ (rowAt 313 = data_313 ∧ Good (rowAt 313) ∧ EntryGood 313) ∧ (rowAt 314 = data_314 ∧ Good (rowAt 314) ∧ EntryGood 314) ∧ (rowAt 315 = data_315 ∧ Good (rowAt 315) ∧ EntryGood 315) ∧ True := by
  exact ⟨⟨row_312, good_312, entry_good_312⟩, ⟨row_313, good_313, entry_good_313⟩, ⟨row_314, good_314, entry_good_314⟩, ⟨row_315, good_315, entry_good_315⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
