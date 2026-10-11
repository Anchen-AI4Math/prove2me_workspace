import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_15 (j : ℕ) (hj : j < 20) : entryAt (306 + j) = tableChunk_15[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_19 : rowAt 19 = data_19 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.1).1
theorem row_97 : rowAt 97 = data_97 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.1).1
theorem row_115 : rowAt 115 = data_115 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_165 : rowAt 165 = data_165 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.1).1
theorem row_195 : rowAt 195 = data_195 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.1).1
theorem row_205 : rowAt 205 = data_205 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_255 : rowAt 255 = data_255 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_267 : rowAt 267 = data_267 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_278 : rowAt 278 = data_278 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_313 : rowAt 313 = data_313 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_324_checked : entryAt 324 = entry_324 := by
  rw [entry_chunk_15 18 (by decide)]
  decide +kernel
theorem row_324 : rowAt 324 = data_324 := by
  rw [rowAt, dif_neg (by decide : ¬ 324 < 6), entry_324_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨298, 0, 3, 4⟩ (rowAt 298)] = data_324
  rw [row_6, row_298]
  apply row_ext <;> decide +kernel
theorem entry_good_324 : EntryGood 324 := by
  unfold EntryGood
  rw [entry_324_checked]
  decide +kernel
theorem good_324 : Good (rowAt 324) := by
  rw [row_324]
  unfold Good
  decide +kernel

theorem entry_325_checked : entryAt 325 = entry_325 := by
  rw [entry_chunk_15 19 (by decide)]
  decide +kernel
theorem row_325 : rowAt 325 = data_325 := by
  rw [rowAt, dif_neg (by decide : ¬ 325 < 6), entry_325_checked]
  change forkRow [placeRow ⟨25, 0, 6, 5⟩ (rowAt 25), placeRow ⟨313, 1, 6, 4⟩ (rowAt 313), placeRow ⟨24, 2, 6, 3⟩ (rowAt 24)] = data_325
  rw [row_25, row_313, row_24]
  apply row_ext <;> decide +kernel
theorem entry_good_325 : EntryGood 325 := by
  unfold EntryGood
  rw [entry_325_checked]
  decide +kernel
theorem good_325 : Good (rowAt 325) := by
  rw [row_325]
  unfold Good
  decide +kernel

theorem entry_326_checked : entryAt 326 = entry_326 := by
  rw [entry_chunk_16 0 (by decide)]
  decide +kernel
theorem row_326 : rowAt 326 = data_326 := by
  rw [rowAt, dif_neg (by decide : ¬ 326 < 6), entry_326_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨255, 7, 0, 4⟩ (rowAt 255)] = data_326
  rw [row_63, row_255]
  apply row_ext <;> decide +kernel
theorem entry_good_326 : EntryGood 326 := by
  unfold EntryGood
  rw [entry_326_checked]
  decide +kernel
theorem good_326 : Good (rowAt 326) := by
  rw [row_326]
  unfold Good
  decide +kernel

theorem entry_327_checked : entryAt 327 = entry_327 := by
  rw [entry_chunk_16 1 (by decide)]
  decide +kernel
theorem row_327 : rowAt 327 = data_327 := by
  rw [rowAt, dif_neg (by decide : ¬ 327 < 6), entry_327_checked]
  change forkRow [placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨195, 4, 2, 4⟩ (rowAt 195), placeRow ⟨195, 0, 6, 4⟩ (rowAt 195), placeRow ⟨24, 6, 2, 3⟩ (rowAt 24)] = data_327
  rw [row_24, row_195]
  apply row_ext <;> decide +kernel
theorem entry_good_327 : EntryGood 327 := by
  unfold EntryGood
  rw [entry_327_checked]
  decide +kernel
theorem good_327 : Good (rowAt 327) := by
  rw [row_327]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 324 = data_324 ∧ Good (rowAt 324) ∧ EntryGood 324) ∧ (rowAt 325 = data_325 ∧ Good (rowAt 325) ∧ EntryGood 325) ∧ (rowAt 326 = data_326 ∧ Good (rowAt 326) ∧ EntryGood 326) ∧ (rowAt 327 = data_327 ∧ Good (rowAt 327) ∧ EntryGood 327) ∧ True := by
  exact ⟨⟨row_324, good_324, entry_good_324⟩, ⟨row_325, good_325, entry_good_325⟩, ⟨row_326, good_326, entry_good_326⟩, ⟨row_327, good_327, entry_good_327⟩, trivial⟩
