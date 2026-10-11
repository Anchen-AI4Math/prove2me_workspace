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
theorem entry_492_checked : entryAt 492 = entry_492 := by
  rw [entry_chunk_24 6 (by decide)]
  decide +kernel
theorem row_492 : rowAt 492 = data_492 := by
  rw [rowAt, dif_neg (by decide : ¬ 492 < 6), entry_492_checked]
  change forkRow [placeRow ⟨62, 4, 3, 4⟩ (rowAt 62), placeRow ⟨107, 4, 3, 4⟩ (rowAt 107), placeRow ⟨487, 0, 6, 6⟩ (rowAt 487)] = data_492
  rw [row_62, row_107, row_487]
  apply row_ext <;> decide +kernel
theorem entry_good_492 : EntryGood 492 := by
  unfold EntryGood
  rw [entry_492_checked]
  decide +kernel
theorem good_492 : Good (rowAt 492) := by
  rw [row_492]
  unfold Good
  decide +kernel

theorem entry_493_checked : entryAt 493 = entry_493 := by
  rw [entry_chunk_24 7 (by decide)]
  decide +kernel
theorem row_493 : rowAt 493 = data_493 := by
  rw [rowAt, dif_neg (by decide : ¬ 493 < 6), entry_493_checked]
  change forkRow [placeRow ⟨225, 0, 1, 4⟩ (rowAt 225), placeRow ⟨455, 0, 5, 3⟩ (rowAt 455), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨221, 0, 5, 4⟩ (rowAt 221)] = data_493
  rw [row_225, row_455, row_236, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_493 : EntryGood 493 := by
  unfold EntryGood
  rw [entry_493_checked]
  decide +kernel
theorem good_493 : Good (rowAt 493) := by
  rw [row_493]
  unfold Good
  decide +kernel

theorem entry_494_checked : entryAt 494 = entry_494 := by
  rw [entry_chunk_24 8 (by decide)]
  decide +kernel
theorem row_494 : rowAt 494 = data_494 := by
  rw [rowAt, dif_neg (by decide : ¬ 494 < 6), entry_494_checked]
  change forkRow [placeRow ⟨297, 4, 4, 5⟩ (rowAt 297), placeRow ⟨268, 4, 1, 5⟩ (rowAt 268), placeRow ⟨162, 5, 5, 4⟩ (rowAt 162)] = data_494
  rw [row_297, row_268, row_162]
  apply row_ext <;> decide +kernel
theorem entry_good_494 : EntryGood 494 := by
  unfold EntryGood
  rw [entry_494_checked]
  decide +kernel
theorem good_494 : Good (rowAt 494) := by
  rw [row_494]
  unfold Good
  decide +kernel

theorem entry_495_checked : entryAt 495 = entry_495 := by
  rw [entry_chunk_24 9 (by decide)]
  decide +kernel
theorem row_495 : rowAt 495 = data_495 := by
  rw [rowAt, dif_neg (by decide : ¬ 495 < 6), entry_495_checked]
  change forkRow [placeRow ⟨25, 6, 1, 3⟩ (rowAt 25), placeRow ⟨167, 4, 1, 4⟩ (rowAt 167), placeRow ⟨456, 4, 1, 4⟩ (rowAt 456)] = data_495
  rw [row_25, row_167, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_495 : EntryGood 495 := by
  unfold EntryGood
  rw [entry_495_checked]
  decide +kernel
theorem good_495 : Good (rowAt 495) := by
  rw [row_495]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 492 = data_492 ∧ Good (rowAt 492) ∧ EntryGood 492) ∧ (rowAt 493 = data_493 ∧ Good (rowAt 493) ∧ EntryGood 493) ∧ (rowAt 494 = data_494 ∧ Good (rowAt 494) ∧ EntryGood 494) ∧ (rowAt 495 = data_495 ∧ Good (rowAt 495) ∧ EntryGood 495) ∧ True := by
  exact ⟨⟨row_492, good_492, entry_good_492⟩, ⟨row_493, good_493, entry_good_493⟩, ⟨row_494, good_494, entry_good_494⟩, ⟨row_495, good_495, entry_good_495⟩, trivial⟩
