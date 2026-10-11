import Definitions.Def_Snaky35Cache09
import Solutions.SnakyMilestones.Certificate35Part08
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_288_checked : entryAt 288 = entry_288 := by
  rw [entry_chunk_14 2 (by decide)]
  decide +kernel
theorem row_288 : rowAt 288 = data_288 := by
  rw [rowAt, dif_neg (by decide : ¬ 288 < 6), entry_288_checked]
  change forkRow [placeRow ⟨130, 1, 4, 2⟩ (rowAt 130), placeRow ⟨96, 0, 1, 4⟩ (rowAt 96)] = data_288
  rw [row_130, row_96]
  apply row_ext <;> decide +kernel
theorem entry_good_288 : EntryGood 288 := by
  unfold EntryGood
  rw [entry_288_checked]
  decide +kernel
theorem good_288 : Good (rowAt 288) := by
  rw [row_288]
  unfold Good
  decide +kernel

theorem entry_289_checked : entryAt 289 = entry_289 := by
  rw [entry_chunk_14 3 (by decide)]
  decide +kernel
theorem row_289 : rowAt 289 = data_289 := by
  rw [rowAt, dif_neg (by decide : ¬ 289 < 6), entry_289_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨279, 0, 2, 4⟩ (rowAt 279)] = data_289
  rw [row_6, row_279]
  apply row_ext <;> decide +kernel
theorem entry_good_289 : EntryGood 289 := by
  unfold EntryGood
  rw [entry_289_checked]
  decide +kernel
theorem good_289 : Good (rowAt 289) := by
  rw [row_289]
  unfold Good
  decide +kernel

theorem entry_290_checked : entryAt 290 = entry_290 := by
  rw [entry_chunk_14 4 (by decide)]
  decide +kernel
theorem row_290 : rowAt 290 = data_290 := by
  rw [rowAt, dif_neg (by decide : ¬ 290 < 6), entry_290_checked]
  change forkRow [placeRow ⟨67, 2, 5, 2⟩ (rowAt 67), placeRow ⟨231, 4, 5, 5⟩ (rowAt 231)] = data_290
  rw [row_67, row_231]
  apply row_ext <;> decide +kernel
theorem entry_good_290 : EntryGood 290 := by
  unfold EntryGood
  rw [entry_290_checked]
  decide +kernel
theorem good_290 : Good (rowAt 290) := by
  rw [row_290]
  unfold Good
  decide +kernel

theorem entry_291_checked : entryAt 291 = entry_291 := by
  rw [entry_chunk_14 5 (by decide)]
  decide +kernel
theorem row_291 : rowAt 291 = data_291 := by
  rw [rowAt, dif_neg (by decide : ¬ 291 < 6), entry_291_checked]
  change forkRow [placeRow ⟨89, 3, 3, 4⟩ (rowAt 89), placeRow ⟨202, 0, 8, 4⟩ (rowAt 202), placeRow ⟨55, 4, 3, 4⟩ (rowAt 55)] = data_291
  rw [row_89, row_202, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_291 : EntryGood 291 := by
  unfold EntryGood
  rw [entry_291_checked]
  decide +kernel
theorem good_291 : Good (rowAt 291) := by
  rw [row_291]
  unfold Good
  decide +kernel


theorem block09_group00_piece00_correct : (rowAt 288 = data_288 ∧ Good (rowAt 288) ∧ EntryGood 288) ∧ (rowAt 289 = data_289 ∧ Good (rowAt 289) ∧ EntryGood 289) ∧ (rowAt 290 = data_290 ∧ Good (rowAt 290) ∧ EntryGood 290) ∧ (rowAt 291 = data_291 ∧ Good (rowAt 291) ∧ EntryGood 291) ∧ True := by
  exact ⟨⟨row_288, good_288, entry_good_288⟩, ⟨row_289, good_289, entry_good_289⟩, ⟨row_290, good_290, entry_good_290⟩, ⟨row_291, good_291, entry_good_291⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
