import Definitions.Def_Snaky35Cache15
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_24 (j : ℕ) (hj : j < 20) : entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_36 : rowAt 36 = data_36 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_232 : rowAt 232 = data_232 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_316 : rowAt 316 = data_316 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_351 : rowAt 351 = data_351 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_410 : rowAt 410 = data_410 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_419 : rowAt 419 = data_419 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.1).1
theorem row_420 : rowAt 420 = data_420 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.1).1
theorem row_478 : rowAt 478 = data_478 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_493 : rowAt 493 = data_493 := (OAI.SnakyCertificate.MilestoneChecks.block15_group01_correct.2.2.2.2.2.1).1
theorem row_494 : rowAt 494 = data_494 := (OAI.SnakyCertificate.MilestoneChecks.block15_group01_correct.2.2.2.2.2.2.1).1
theorem entry_500_checked : entryAt 500 = entry_500 := by
  rw [entry_chunk_24 14 (by decide)]
  decide +kernel
theorem row_500 : rowAt 500 = data_500 := by
  rw [rowAt, dif_neg (by decide : ¬ 500 < 6), entry_500_checked]
  change forkRow [placeRow ⟨1, 5, 3, 6⟩ (rowAt 1), placeRow ⟨351, 0, 5, 4⟩ (rowAt 351)] = data_500
  rw [row_1, row_351]
  apply row_ext <;> decide +kernel
theorem entry_good_500 : EntryGood 500 := by
  unfold EntryGood
  rw [entry_500_checked]
  decide +kernel
theorem good_500 : Good (rowAt 500) := by
  rw [row_500]
  unfold Good
  decide +kernel

theorem entry_501_checked : entryAt 501 = entry_501 := by
  rw [entry_chunk_24 15 (by decide)]
  decide +kernel
theorem row_501 : rowAt 501 = data_501 := by
  rw [rowAt, dif_neg (by decide : ¬ 501 < 6), entry_501_checked]
  change forkRow [placeRow ⟨6, 4, 0, 5⟩ (rowAt 6), placeRow ⟨316, 0, 1, 3⟩ (rowAt 316)] = data_501
  rw [row_6, row_316]
  apply row_ext <;> decide +kernel
theorem entry_good_501 : EntryGood 501 := by
  unfold EntryGood
  rw [entry_501_checked]
  decide +kernel
theorem good_501 : Good (rowAt 501) := by
  rw [row_501]
  unfold Good
  decide +kernel

theorem entry_502_checked : entryAt 502 = entry_502 := by
  rw [entry_chunk_24 16 (by decide)]
  decide +kernel
theorem row_502 : rowAt 502 = data_502 := by
  rw [rowAt, dif_neg (by decide : ¬ 502 < 6), entry_502_checked]
  change forkRow [placeRow ⟨215, 6, 2, 3⟩ (rowAt 215), placeRow ⟨232, 0, 4, 3⟩ (rowAt 232), placeRow ⟨192, 7, 1, 4⟩ (rowAt 192), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173), placeRow ⟨271, 2, 2, 3⟩ (rowAt 271)] = data_502
  rw [row_215, row_232, row_192, row_173, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_502 : EntryGood 502 := by
  unfold EntryGood
  rw [entry_502_checked]
  decide +kernel
theorem good_502 : Good (rowAt 502) := by
  rw [row_502]
  unfold Good
  decide +kernel

theorem entry_503_checked : entryAt 503 = entry_503 := by
  rw [entry_chunk_24 17 (by decide)]
  decide +kernel
theorem row_503 : rowAt 503 = data_503 := by
  rw [rowAt, dif_neg (by decide : ¬ 503 < 6), entry_503_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨420, 1, 7, 2⟩ (rowAt 420), placeRow ⟨419, 1, 7, 4⟩ (rowAt 419)] = data_503
  rw [row_63, row_55, row_420, row_419]
  apply row_ext <;> decide +kernel
theorem entry_good_503 : EntryGood 503 := by
  unfold EntryGood
  rw [entry_503_checked]
  decide +kernel
theorem good_503 : Good (rowAt 503) := by
  rw [row_503]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 500 = data_500 ∧ Good (rowAt 500) ∧ EntryGood 500) ∧ (rowAt 501 = data_501 ∧ Good (rowAt 501) ∧ EntryGood 501) ∧ (rowAt 502 = data_502 ∧ Good (rowAt 502) ∧ EntryGood 502) ∧ (rowAt 503 = data_503 ∧ Good (rowAt 503) ∧ EntryGood 503) ∧ True := by
  exact ⟨⟨row_500, good_500, entry_good_500⟩, ⟨row_501, good_501, entry_good_501⟩, ⟨row_502, good_502, entry_good_502⟩, ⟨row_503, good_503, entry_good_503⟩, trivial⟩
