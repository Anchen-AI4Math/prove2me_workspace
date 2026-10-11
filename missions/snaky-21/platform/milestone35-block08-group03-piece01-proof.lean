import Definitions.Def_Snaky35Cache08
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_13 (j : ℕ) (hj : j < 20) : entryAt (266 + j) = tableChunk_13[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_14 (j : ℕ) (hj : j < 20) : entryAt (286 + j) = tableChunk_14[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_45 : rowAt 45 = data_45 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_46 : rowAt 46 = data_46 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_56 : rowAt 56 = data_56 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_116 : rowAt 116 = data_116 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_184 : rowAt 184 = data_184 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_189 : rowAt 189 = data_189 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_196 : rowAt 196 = data_196 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.1).1
theorem row_224 : rowAt 224 = data_224 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_group00_correct.2.2.2.2.2.1).1
theorem row_264 : rowAt 264 = data_264 := (OAI.SnakyCertificate.MilestoneChecks.block08_group01_correct.1).1
theorem row_265 : rowAt 265 = data_265 := (OAI.SnakyCertificate.MilestoneChecks.block08_group01_correct.2.1).1
theorem row_273 : rowAt 273 = data_273 := (OAI.SnakyCertificate.MilestoneChecks.block08_group02_correct.2.1).1
theorem entry_284_checked : entryAt 284 = entry_284 := by
  rw [entry_chunk_13 18 (by decide)]
  decide +kernel
theorem row_284 : rowAt 284 = data_284 := by
  rw [rowAt, dif_neg (by decide : ¬ 284 < 6), entry_284_checked]
  change forkRow [placeRow ⟨45, 1, 4, 5⟩ (rowAt 45), placeRow ⟨224, 0, 5, 4⟩ (rowAt 224), placeRow ⟨46, 3, 4, 5⟩ (rowAt 46)] = data_284
  rw [row_45, row_224, row_46]
  apply row_ext <;> decide +kernel
theorem entry_good_284 : EntryGood 284 := by
  unfold EntryGood
  rw [entry_284_checked]
  decide +kernel
theorem good_284 : Good (rowAt 284) := by
  rw [row_284]
  unfold Good
  decide +kernel

theorem entry_285_checked : entryAt 285 = entry_285 := by
  rw [entry_chunk_13 19 (by decide)]
  decide +kernel
theorem row_285 : rowAt 285 = data_285 := by
  rw [rowAt, dif_neg (by decide : ¬ 285 < 6), entry_285_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨273, 0, 6, 4⟩ (rowAt 273)] = data_285
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_285 : EntryGood 285 := by
  unfold EntryGood
  rw [entry_285_checked]
  decide +kernel
theorem good_285 : Good (rowAt 285) := by
  rw [row_285]
  unfold Good
  decide +kernel

theorem entry_286_checked : entryAt 286 = entry_286 := by
  rw [entry_chunk_14 0 (by decide)]
  decide +kernel
theorem row_286 : rowAt 286 = data_286 := by
  rw [rowAt, dif_neg (by decide : ¬ 286 < 6), entry_286_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_286
  rw [row_6, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_286 : EntryGood 286 := by
  unfold EntryGood
  rw [entry_286_checked]
  decide +kernel
theorem good_286 : Good (rowAt 286) := by
  rw [row_286]
  unfold Good
  decide +kernel

theorem entry_287_checked : entryAt 287 = entry_287 := by
  rw [entry_chunk_14 1 (by decide)]
  decide +kernel
theorem row_287 : rowAt 287 = data_287 := by
  rw [rowAt, dif_neg (by decide : ¬ 287 < 6), entry_287_checked]
  change forkRow [placeRow ⟨64, 0, 1, 3⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨56, 0, 5, 4⟩ (rowAt 56), placeRow ⟨264, 4, 4, 5⟩ (rowAt 264)] = data_287
  rw [row_64, row_55, row_56, row_264]
  apply row_ext <;> decide +kernel
theorem entry_good_287 : EntryGood 287 := by
  unfold EntryGood
  rw [entry_287_checked]
  decide +kernel
theorem good_287 : Good (rowAt 287) := by
  rw [row_287]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 284 = data_284 ∧ Good (rowAt 284) ∧ EntryGood 284) ∧ (rowAt 285 = data_285 ∧ Good (rowAt 285) ∧ EntryGood 285) ∧ (rowAt 286 = data_286 ∧ Good (rowAt 286) ∧ EntryGood 286) ∧ (rowAt 287 = data_287 ∧ Good (rowAt 287) ∧ EntryGood 287) ∧ True := by
  exact ⟨⟨row_284, good_284, entry_good_284⟩, ⟨row_285, good_285, entry_good_285⟩, ⟨row_286, good_286, entry_good_286⟩, ⟨row_287, good_287, entry_good_287⟩, trivial⟩
