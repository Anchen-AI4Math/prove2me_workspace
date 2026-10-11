import Definitions.Def_Snaky35Cache16
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group03_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_26 (j : ℕ) (hj : j < 20) : entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_51 : rowAt 51 = data_51 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_88 : rowAt 88 = data_88 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_142 : rowAt 142 = data_142 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_160 : rowAt 160 = data_160 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_194 : rowAt 194 = data_194 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_244 : rowAt 244 = data_244 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_307 : rowAt 307 = data_307 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_318 : rowAt 318 = data_318 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_330 : rowAt 330 = data_330 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_334 : rowAt 334 = data_334 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_373 : rowAt 373 = data_373 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_412 : rowAt 412 = data_412 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_428 : rowAt 428 = data_428 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_442 : rowAt 442 = data_442 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_470 : rowAt 470 = data_470 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_488 : rowAt 488 = data_488 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.1).1
theorem row_493 : rowAt 493 = data_493 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_501 : rowAt 501 = data_501 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_516 : rowAt 516 = data_516 := (OAI.SnakyCertificate.MilestoneChecks.block16_group00_correct.2.2.2.2.1).1
theorem row_534 : rowAt 534 = data_534 := (OAI.SnakyCertificate.MilestoneChecks.block16_group02_correct.2.2.2.2.2.2.1).1
theorem row_536 : rowAt 536 = data_536 := (OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece00_correct.1).1
theorem entry_540_checked : entryAt 540 = entry_540 := by
  rw [entry_chunk_26 14 (by decide)]
  decide +kernel
theorem row_540 : rowAt 540 = data_540 := by
  rw [rowAt, dif_neg (by decide : ¬ 540 < 6), entry_540_checked]
  change forkRow [placeRow ⟨334, 0, 4, 3⟩ (rowAt 334), placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨88, 3, 4, 3⟩ (rowAt 88), placeRow ⟨536, 0, 5, 4⟩ (rowAt 536)] = data_540
  rw [row_334, row_51, row_88, row_536]
  apply row_ext <;> decide +kernel
theorem entry_good_540 : EntryGood 540 := by
  unfold EntryGood
  rw [entry_540_checked]
  decide +kernel
theorem good_540 : Good (rowAt 540) := by
  rw [row_540]
  unfold Good
  decide +kernel

theorem entry_541_checked : entryAt 541 = entry_541 := by
  rw [entry_chunk_26 15 (by decide)]
  decide +kernel
theorem row_541 : rowAt 541 = data_541 := by
  rw [rowAt, dif_neg (by decide : ¬ 541 < 6), entry_541_checked]
  change forkRow [placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨142, 7, 4, 1⟩ (rowAt 142), placeRow ⟨160, 3, 4, 1⟩ (rowAt 160), placeRow ⟨194, 0, 5, 3⟩ (rowAt 194), placeRow ⟨501, 4, 1, 2⟩ (rowAt 501), placeRow ⟨412, 0, 5, 3⟩ (rowAt 412)] = data_541
  rw [row_236, row_142, row_160, row_194, row_501, row_412]
  apply row_ext <;> decide +kernel
theorem entry_good_541 : EntryGood 541 := by
  unfold EntryGood
  rw [entry_541_checked]
  decide +kernel
theorem good_541 : Good (rowAt 541) := by
  rw [row_541]
  unfold Good
  decide +kernel

theorem entry_542_checked : entryAt 542 = entry_542 := by
  rw [entry_chunk_26 16 (by decide)]
  decide +kernel
theorem row_542 : rowAt 542 = data_542 := by
  rw [rowAt, dif_neg (by decide : ¬ 542 < 6), entry_542_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442)] = data_542
  rw [row_6, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_542 : EntryGood 542 := by
  unfold EntryGood
  rw [entry_542_checked]
  decide +kernel
theorem good_542 : Good (rowAt 542) := by
  rw [row_542]
  unfold Good
  decide +kernel

theorem entry_543_checked : entryAt 543 = entry_543 := by
  rw [entry_chunk_26 17 (by decide)]
  decide +kernel
theorem row_543 : rowAt 543 = data_543 := by
  rw [rowAt, dif_neg (by decide : ¬ 543 < 6), entry_543_checked]
  change forkRow [placeRow ⟨493, 3, 2, 6⟩ (rowAt 493), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318)] = data_543
  rw [row_493, row_107, row_318]
  apply row_ext <;> decide +kernel
theorem entry_good_543 : EntryGood 543 := by
  unfold EntryGood
  rw [entry_543_checked]
  decide +kernel
theorem good_543 : Good (rowAt 543) := by
  rw [row_543]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 540 = data_540 ∧ Good (rowAt 540) ∧ EntryGood 540) ∧ (rowAt 541 = data_541 ∧ Good (rowAt 541) ∧ EntryGood 541) ∧ (rowAt 542 = data_542 ∧ Good (rowAt 542) ∧ EntryGood 542) ∧ (rowAt 543 = data_543 ∧ Good (rowAt 543) ∧ EntryGood 543) ∧ True := by
  exact ⟨⟨row_540, good_540, entry_good_540⟩, ⟨row_541, good_541, entry_good_541⟩, ⟨row_542, good_542, entry_good_542⟩, ⟨row_543, good_543, entry_good_543⟩, trivial⟩
