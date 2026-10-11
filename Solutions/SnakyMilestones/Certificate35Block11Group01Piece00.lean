import Definitions.Def_Snaky35Cache11
import Solutions.SnakyMilestones.Certificate35Block11Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_360_checked : entryAt 360 = entry_360 := by
  rw [entry_chunk_17 14 (by decide)]
  decide +kernel
theorem row_360 : rowAt 360 = data_360 := by
  rw [rowAt, dif_neg (by decide : ¬ 360 < 6), entry_360_checked]
  change forkRow [placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨337, 0, 5, 2⟩ (rowAt 337), placeRow ⟨228, 4, 5, 2⟩ (rowAt 228)] = data_360
  rw [row_155, row_7, row_337, row_228]
  apply row_ext <;> decide +kernel
theorem entry_good_360 : EntryGood 360 := by
  unfold EntryGood
  rw [entry_360_checked]
  decide +kernel
theorem good_360 : Good (rowAt 360) := by
  rw [row_360]
  unfold Good
  decide +kernel

theorem entry_361_checked : entryAt 361 = entry_361 := by
  rw [entry_chunk_17 15 (by decide)]
  decide +kernel
theorem row_361 : rowAt 361 = data_361 := by
  rw [rowAt, dif_neg (by decide : ¬ 361 < 6), entry_361_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨352, 0, 4, 5⟩ (rowAt 352)] = data_361
  rw [row_6, row_352]
  apply row_ext <;> decide +kernel
theorem entry_good_361 : EntryGood 361 := by
  unfold EntryGood
  rw [entry_361_checked]
  decide +kernel
theorem good_361 : Good (rowAt 361) := by
  rw [row_361]
  unfold Good
  decide +kernel

theorem entry_362_checked : entryAt 362 = entry_362 := by
  rw [entry_chunk_17 16 (by decide)]
  decide +kernel
theorem row_362 : rowAt 362 = data_362 := by
  rw [rowAt, dif_neg (by decide : ¬ 362 < 6), entry_362_checked]
  change forkRow [placeRow ⟨4, 0, 3, 4⟩ (rowAt 4), placeRow ⟨345, 0, 4, 3⟩ (rowAt 345)] = data_362
  rw [row_4, row_345]
  apply row_ext <;> decide +kernel
theorem entry_good_362 : EntryGood 362 := by
  unfold EntryGood
  rw [entry_362_checked]
  decide +kernel
theorem good_362 : Good (rowAt 362) := by
  rw [row_362]
  unfold Good
  decide +kernel

theorem entry_363_checked : entryAt 363 = entry_363 := by
  rw [entry_chunk_17 17 (by decide)]
  decide +kernel
theorem row_363 : rowAt 363 = data_363 := by
  rw [rowAt, dif_neg (by decide : ¬ 363 < 6), entry_363_checked]
  change forkRow [placeRow ⟨137, 1, 4, 2⟩ (rowAt 137), placeRow ⟨248, 0, 2, 4⟩ (rowAt 248)] = data_363
  rw [row_137, row_248]
  apply row_ext <;> decide +kernel
theorem entry_good_363 : EntryGood 363 := by
  unfold EntryGood
  rw [entry_363_checked]
  decide +kernel
theorem good_363 : Good (rowAt 363) := by
  rw [row_363]
  unfold Good
  decide +kernel


theorem block11_group01_piece00_correct : (rowAt 360 = data_360 ∧ Good (rowAt 360) ∧ EntryGood 360) ∧ (rowAt 361 = data_361 ∧ Good (rowAt 361) ∧ EntryGood 361) ∧ (rowAt 362 = data_362 ∧ Good (rowAt 362) ∧ EntryGood 362) ∧ (rowAt 363 = data_363 ∧ Good (rowAt 363) ∧ EntryGood 363) ∧ True := by
  exact ⟨⟨row_360, good_360, entry_good_360⟩, ⟨row_361, good_361, entry_good_361⟩, ⟨row_362, good_362, entry_good_362⟩, ⟨row_363, good_363, entry_good_363⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
