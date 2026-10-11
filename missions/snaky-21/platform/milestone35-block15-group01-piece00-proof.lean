import Definitions.Def_Snaky35Cache15
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_24 (j : ℕ) (hj : j < 20) : entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_62 : rowAt 62 = data_62 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_111 : rowAt 111 = data_111 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_221 : rowAt 221 = data_221 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_225 : rowAt 225 = data_225 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_247 : rowAt 247 = data_247 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_268 : rowAt 268 = data_268 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_273 : rowAt 273 = data_273 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_297 : rowAt 297 = data_297 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_356 : rowAt 356 = data_356 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.1).1
theorem row_455 : rowAt 455 = data_455 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.1).1
theorem row_456 : rowAt 456 = data_456 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.1).1
theorem row_470 : rowAt 470 = data_470 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_471 : rowAt 471 = data_471 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_487 : rowAt 487 = data_487 := (OAI.SnakyCertificate.MilestoneChecks.block15_group00_correct.2.2.2.2.2.2.2.1).1
theorem entry_488_checked : entryAt 488 = entry_488 := by
  rw [entry_chunk_24 2 (by decide)]
  decide +kernel
theorem row_488 : rowAt 488 = data_488 := by
  rw [rowAt, dif_neg (by decide : ¬ 488 < 6), entry_488_checked]
  change forkRow [placeRow ⟨0, 6, 6, 4⟩ (rowAt 0), placeRow ⟨247, 0, 2, 5⟩ (rowAt 247)] = data_488
  rw [row_0, row_247]
  apply row_ext <;> decide +kernel
theorem entry_good_488 : EntryGood 488 := by
  unfold EntryGood
  rw [entry_488_checked]
  decide +kernel
theorem good_488 : Good (rowAt 488) := by
  rw [row_488]
  unfold Good
  decide +kernel

theorem entry_489_checked : entryAt 489 = entry_489 := by
  rw [entry_chunk_24 3 (by decide)]
  decide +kernel
theorem row_489 : rowAt 489 = data_489 := by
  rw [rowAt, dif_neg (by decide : ¬ 489 < 6), entry_489_checked]
  change forkRow [placeRow ⟨356, 1, 3, 3⟩ (rowAt 356), placeRow ⟨197, 4, 1, 4⟩ (rowAt 197), placeRow ⟨172, 6, 1, 4⟩ (rowAt 172)] = data_489
  rw [row_356, row_197, row_172]
  apply row_ext <;> decide +kernel
theorem entry_good_489 : EntryGood 489 := by
  unfold EntryGood
  rw [entry_489_checked]
  decide +kernel
theorem good_489 : Good (rowAt 489) := by
  rw [row_489]
  unfold Good
  decide +kernel

theorem entry_490_checked : entryAt 490 = entry_490 := by
  rw [entry_chunk_24 4 (by decide)]
  decide +kernel
theorem row_490 : rowAt 490 = data_490 := by
  rw [rowAt, dif_neg (by decide : ¬ 490 < 6), entry_490_checked]
  change forkRow [placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨470, 1, 5, 1⟩ (rowAt 470), placeRow ⟨111, 0, 3, 1⟩ (rowAt 111)] = data_490
  rw [row_64, row_471, row_470, row_111]
  apply row_ext <;> decide +kernel
theorem entry_good_490 : EntryGood 490 := by
  unfold EntryGood
  rw [entry_490_checked]
  decide +kernel
theorem good_490 : Good (rowAt 490) := by
  rw [row_490]
  unfold Good
  decide +kernel

theorem entry_491_checked : entryAt 491 = entry_491 := by
  rw [entry_chunk_24 5 (by decide)]
  decide +kernel
theorem row_491 : rowAt 491 = data_491 := by
  rw [rowAt, dif_neg (by decide : ¬ 491 < 6), entry_491_checked]
  change forkRow [placeRow ⟨6, 3, 3, 5⟩ (rowAt 6), placeRow ⟨273, 0, 5, 4⟩ (rowAt 273)] = data_491
  rw [row_6, row_273]
  apply row_ext <;> decide +kernel
theorem entry_good_491 : EntryGood 491 := by
  unfold EntryGood
  rw [entry_491_checked]
  decide +kernel
theorem good_491 : Good (rowAt 491) := by
  rw [row_491]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 488 = data_488 ∧ Good (rowAt 488) ∧ EntryGood 488) ∧ (rowAt 489 = data_489 ∧ Good (rowAt 489) ∧ EntryGood 489) ∧ (rowAt 490 = data_490 ∧ Good (rowAt 490) ∧ EntryGood 490) ∧ (rowAt 491 = data_491 ∧ Good (rowAt 491) ∧ EntryGood 491) ∧ True := by
  exact ⟨⟨row_488, good_488, entry_good_488⟩, ⟨row_489, good_489, entry_good_489⟩, ⟨row_490, good_490, entry_good_490⟩, ⟨row_491, good_491, entry_good_491⟩, trivial⟩
