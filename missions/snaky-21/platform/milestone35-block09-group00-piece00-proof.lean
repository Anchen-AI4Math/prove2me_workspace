import Definitions.Def_Snaky35Cache09
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_14 (j : ℕ) (hj : j < 20) : entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_39 : rowAt 39 = data_39 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.1).1
theorem row_79 : rowAt 79 = data_79 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_89 : rowAt 89 = data_89 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.1).1
theorem row_130 : rowAt 130 = data_130 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.1).1
theorem row_196 : rowAt 196 = data_196 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.1).1
theorem row_202 : rowAt 202 = data_202 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_219 : rowAt 219 = data_219 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_231 : rowAt 231 = data_231 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.1).1
theorem row_265 : rowAt 265 = data_265 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_279 : rowAt 279 = data_279 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_280 : rowAt 280 = data_280 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
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


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 288 = data_288 ∧ Good (rowAt 288) ∧ EntryGood 288) ∧ (rowAt 289 = data_289 ∧ Good (rowAt 289) ∧ EntryGood 289) ∧ (rowAt 290 = data_290 ∧ Good (rowAt 290) ∧ EntryGood 290) ∧ (rowAt 291 = data_291 ∧ Good (rowAt 291) ∧ EntryGood 291) ∧ True := by
  exact ⟨⟨row_288, good_288, entry_good_288⟩, ⟨row_289, good_289, entry_good_289⟩, ⟨row_290, good_290, entry_good_290⟩, ⟨row_291, good_291, entry_good_291⟩, trivial⟩
