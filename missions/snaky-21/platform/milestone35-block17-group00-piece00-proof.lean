import Definitions.Def_Snaky35Cache17
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_26 (j : ℕ) (hj : j < 20) : entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_27 (j : ℕ) (hj : j < 20) : entryAt (546 + j) = tableChunk_27[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_153 : rowAt 153 = data_153 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_256 : rowAt 256 = data_256 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_321 : rowAt 321 = data_321 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.1).1
theorem row_326 : rowAt 326 = data_326 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.1).1
theorem row_330 : rowAt 330 = data_330 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_343 : rowAt 343 = data_343 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_385 : rowAt 385 = data_385 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.1).1
theorem row_424 : rowAt 424 = data_424 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.1).1
theorem row_426 : rowAt 426 = data_426 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_448 : rowAt 448 = data_448 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.1).1
theorem row_451 : rowAt 451 = data_451 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.1).1
theorem row_456 : rowAt 456 = data_456 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.1).1
theorem row_482 : rowAt 482 = data_482 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.1).1
theorem row_510 : rowAt 510 = data_510 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_527 : rowAt 527 = data_527 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_529 : rowAt 529 = data_529 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_541 : rowAt 541 = data_541 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_544_checked : entryAt 544 = entry_544 := by
  rw [entry_chunk_26 18 (by decide)]
  decide +kernel
theorem row_544 : rowAt 544 = data_544 := by
  rw [rowAt, dif_neg (by decide : ¬ 544 < 6), entry_544_checked]
  change forkRow [placeRow ⟨263, 2, 7, 4⟩ (rowAt 263), placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨451, 1, 8, 3⟩ (rowAt 451)] = data_544
  rw [row_263, row_9, row_451]
  apply row_ext <;> decide +kernel
theorem entry_good_544 : EntryGood 544 := by
  unfold EntryGood
  rw [entry_544_checked]
  decide +kernel
theorem good_544 : Good (rowAt 544) := by
  rw [row_544]
  unfold Good
  decide +kernel

theorem entry_545_checked : entryAt 545 = entry_545 := by
  rw [entry_chunk_26 19 (by decide)]
  decide +kernel
theorem row_545 : rowAt 545 = data_545 := by
  rw [rowAt, dif_neg (by decide : ¬ 545 < 6), entry_545_checked]
  change forkRow [placeRow ⟨256, 0, 4, 5⟩ (rowAt 256), placeRow ⟨448, 0, 5, 4⟩ (rowAt 448), placeRow ⟨153, 0, 6, 3⟩ (rowAt 153), placeRow ⟨343, 0, 4, 5⟩ (rowAt 343)] = data_545
  rw [row_256, row_448, row_153, row_343]
  apply row_ext <;> decide +kernel
theorem entry_good_545 : EntryGood 545 := by
  unfold EntryGood
  rw [entry_545_checked]
  decide +kernel
theorem good_545 : Good (rowAt 545) := by
  rw [row_545]
  unfold Good
  decide +kernel

theorem entry_546_checked : entryAt 546 = entry_546 := by
  rw [entry_chunk_27 0 (by decide)]
  decide +kernel
theorem row_546 : rowAt 546 = data_546 := by
  rw [rowAt, dif_neg (by decide : ¬ 546 < 6), entry_546_checked]
  change forkRow [placeRow ⟨64, 0, 4, 3⟩ (rowAt 64), placeRow ⟨482, 7, 4, 3⟩ (rowAt 482), placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_546
  rw [row_64, row_482, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_546 : EntryGood 546 := by
  unfold EntryGood
  rw [entry_546_checked]
  decide +kernel
theorem good_546 : Good (rowAt 546) := by
  rw [row_546]
  unfold Good
  decide +kernel

theorem entry_547_checked : entryAt 547 = entry_547 := by
  rw [entry_chunk_27 1 (by decide)]
  decide +kernel
theorem row_547 : rowAt 547 = data_547 := by
  rw [rowAt, dif_neg (by decide : ¬ 547 < 6), entry_547_checked]
  change forkRow [placeRow ⟨443, 0, 7, 5⟩ (rowAt 443), placeRow ⟨510, 4, 7, 5⟩ (rowAt 510), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131)] = data_547
  rw [row_443, row_510, row_131]
  apply row_ext <;> decide +kernel
theorem entry_good_547 : EntryGood 547 := by
  unfold EntryGood
  rw [entry_547_checked]
  decide +kernel
theorem good_547 : Good (rowAt 547) := by
  rw [row_547]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 544 = data_544 ∧ Good (rowAt 544) ∧ EntryGood 544) ∧ (rowAt 545 = data_545 ∧ Good (rowAt 545) ∧ EntryGood 545) ∧ (rowAt 546 = data_546 ∧ Good (rowAt 546) ∧ EntryGood 546) ∧ (rowAt 547 = data_547 ∧ Good (rowAt 547) ∧ EntryGood 547) ∧ True := by
  exact ⟨⟨row_544, good_544, entry_good_544⟩, ⟨row_545, good_545, entry_good_545⟩, ⟨row_546, good_546, entry_good_546⟩, ⟨row_547, good_547, entry_good_547⟩, trivial⟩
