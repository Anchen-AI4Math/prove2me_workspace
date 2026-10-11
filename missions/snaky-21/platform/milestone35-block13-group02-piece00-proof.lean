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
theorem entry_432_checked : entryAt 432 = entry_432 := by
  rw [entry_chunk_21 6 (by decide)]
  decide +kernel
theorem row_432 : rowAt 432 = data_432 := by
  rw [rowAt, dif_neg (by decide : ¬ 432 < 6), entry_432_checked]
  change forkRow [placeRow ⟨42, 3, 4, 3⟩ (rowAt 42), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨274, 0, 4, 3⟩ (rowAt 274)] = data_432
  rw [row_42, row_428, row_274]
  apply row_ext <;> decide +kernel
theorem entry_good_432 : EntryGood 432 := by
  unfold EntryGood
  rw [entry_432_checked]
  decide +kernel
theorem good_432 : Good (rowAt 432) := by
  rw [row_432]
  unfold Good
  decide +kernel

theorem entry_433_checked : entryAt 433 = entry_433 := by
  rw [entry_chunk_21 7 (by decide)]
  decide +kernel
theorem row_433 : rowAt 433 = data_433 := by
  rw [rowAt, dif_neg (by decide : ¬ 433 < 6), entry_433_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨427, 0, 5, 2⟩ (rowAt 427), placeRow ⟨422, 0, 5, 2⟩ (rowAt 422)] = data_433
  rw [row_63, row_7, row_427, row_422]
  apply row_ext <;> decide +kernel
theorem entry_good_433 : EntryGood 433 := by
  unfold EntryGood
  rw [entry_433_checked]
  decide +kernel
theorem good_433 : Good (rowAt 433) := by
  rw [row_433]
  unfold Good
  decide +kernel

theorem entry_434_checked : entryAt 434 = entry_434 := by
  rw [entry_chunk_21 8 (by decide)]
  decide +kernel
theorem row_434 : rowAt 434 = data_434 := by
  rw [rowAt, dif_neg (by decide : ¬ 434 < 6), entry_434_checked]
  change forkRow [placeRow ⟨418, 0, 4, 5⟩ (rowAt 418), placeRow ⟨263, 2, 5, 4⟩ (rowAt 263), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨116, 0, 4, 3⟩ (rowAt 116)] = data_434
  rw [row_418, row_263, row_295, row_176, row_116]
  apply row_ext <;> decide +kernel
theorem entry_good_434 : EntryGood 434 := by
  unfold EntryGood
  rw [entry_434_checked]
  decide +kernel
theorem good_434 : Good (rowAt 434) := by
  rw [row_434]
  unfold Good
  decide +kernel

theorem entry_435_checked : entryAt 435 = entry_435 := by
  rw [entry_chunk_21 9 (by decide)]
  decide +kernel
theorem row_435 : rowAt 435 = data_435 := by
  rw [rowAt, dif_neg (by decide : ¬ 435 < 6), entry_435_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨431, 0, 5, 6⟩ (rowAt 431)] = data_435
  rw [row_6, row_431]
  apply row_ext <;> decide +kernel
theorem entry_good_435 : EntryGood 435 := by
  unfold EntryGood
  rw [entry_435_checked]
  decide +kernel
theorem good_435 : Good (rowAt 435) := by
  rw [row_435]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 432 = data_432 ∧ Good (rowAt 432) ∧ EntryGood 432) ∧ (rowAt 433 = data_433 ∧ Good (rowAt 433) ∧ EntryGood 433) ∧ (rowAt 434 = data_434 ∧ Good (rowAt 434) ∧ EntryGood 434) ∧ (rowAt 435 = data_435 ∧ Good (rowAt 435) ∧ EntryGood 435) ∧ True := by
  exact ⟨⟨row_432, good_432, entry_good_432⟩, ⟨row_433, good_433, entry_good_433⟩, ⟨row_434, good_434, entry_good_434⟩, ⟨row_435, good_435, entry_good_435⟩, trivial⟩
