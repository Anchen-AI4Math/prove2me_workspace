import Definitions.Def_Snaky35Cache13
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group02_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_21 (j : ℕ) (hj : j < 20) : entryAt (426 + j) = tableChunk_21[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_42 : rowAt 42 = data_42 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_51 : rowAt 51 = data_51 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_60 : rowAt 60 = data_60 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_116 : rowAt 116 = data_116 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_149 : rowAt 149 = data_149 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_274 : rowAt 274 = data_274 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_418 : rowAt 418 = data_418 := (OAI.SnakyCertificate.MilestoneChecks.block13_group00_correct.2.2.1).1
theorem row_422 : rowAt 422 = data_422 := (OAI.SnakyCertificate.MilestoneChecks.block13_group00_correct.2.2.2.2.2.2.1).1
theorem row_427 : rowAt 427 = data_427 := (OAI.SnakyCertificate.MilestoneChecks.block13_group01_correct.2.2.2.1).1
theorem row_428 : rowAt 428 = data_428 := (OAI.SnakyCertificate.MilestoneChecks.block13_group01_correct.2.2.2.2.1).1
theorem row_431 : rowAt 431 = data_431 := (OAI.SnakyCertificate.MilestoneChecks.block13_group01_correct.2.2.2.2.2.2.2.1).1
theorem row_432 : rowAt 432 = data_432 := (OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece00_correct.1).1
theorem entry_436_checked : entryAt 436 = entry_436 := by
  rw [entry_chunk_21 10 (by decide)]
  decide +kernel
theorem row_436 : rowAt 436 = data_436 := by
  rw [rowAt, dif_neg (by decide : ¬ 436 < 6), entry_436_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨60, 3, 4, 3⟩ (rowAt 60), placeRow ⟨274, 4, 4, 3⟩ (rowAt 274), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428)] = data_436
  rw [row_51, row_60, row_274, row_428]
  apply row_ext <;> decide +kernel
theorem entry_good_436 : EntryGood 436 := by
  unfold EntryGood
  rw [entry_436_checked]
  decide +kernel
theorem good_436 : Good (rowAt 436) := by
  rw [row_436]
  unfold Good
  decide +kernel

theorem entry_437_checked : entryAt 437 = entry_437 := by
  rw [entry_chunk_21 11 (by decide)]
  decide +kernel
theorem row_437 : rowAt 437 = data_437 := by
  rw [rowAt, dif_neg (by decide : ¬ 437 < 6), entry_437_checked]
  change forkRow [placeRow ⟨55, 7, 4, 0⟩ (rowAt 55), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_437
  rw [row_55, row_427, row_63, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_437 : EntryGood 437 := by
  unfold EntryGood
  rw [entry_437_checked]
  decide +kernel
theorem good_437 : Good (rowAt 437) := by
  rw [row_437]
  unfold Good
  decide +kernel

theorem entry_438_checked : entryAt 438 = entry_438 := by
  rw [entry_chunk_21 12 (by decide)]
  decide +kernel
theorem row_438 : rowAt 438 = data_438 := by
  rw [rowAt, dif_neg (by decide : ¬ 438 < 6), entry_438_checked]
  change forkRow [placeRow ⟨0, 0, 1, 3⟩ (rowAt 0), placeRow ⟨432, 0, 4, 6⟩ (rowAt 432)] = data_438
  rw [row_0, row_432]
  apply row_ext <;> decide +kernel
theorem entry_good_438 : EntryGood 438 := by
  unfold EntryGood
  rw [entry_438_checked]
  decide +kernel
theorem good_438 : Good (rowAt 438) := by
  rw [row_438]
  unfold Good
  decide +kernel

theorem entry_439_checked : entryAt 439 = entry_439 := by
  rw [entry_chunk_21 13 (by decide)]
  decide +kernel
theorem row_439 : rowAt 439 = data_439 := by
  rw [rowAt, dif_neg (by decide : ¬ 439 < 6), entry_439_checked]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨149, 0, 4, 3⟩ (rowAt 149)] = data_439
  rw [row_176, row_295, row_263, row_418, row_149]
  apply row_ext <;> decide +kernel
theorem entry_good_439 : EntryGood 439 := by
  unfold EntryGood
  rw [entry_439_checked]
  decide +kernel
theorem good_439 : Good (rowAt 439) := by
  rw [row_439]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 436 = data_436 ∧ Good (rowAt 436) ∧ EntryGood 436) ∧ (rowAt 437 = data_437 ∧ Good (rowAt 437) ∧ EntryGood 437) ∧ (rowAt 438 = data_438 ∧ Good (rowAt 438) ∧ EntryGood 438) ∧ (rowAt 439 = data_439 ∧ Good (rowAt 439) ∧ EntryGood 439) ∧ True := by
  exact ⟨⟨row_436, good_436, entry_good_436⟩, ⟨row_437, good_437, entry_good_437⟩, ⟨row_438, good_438, entry_good_438⟩, ⟨row_439, good_439, entry_good_439⟩, trivial⟩
