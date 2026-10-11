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
theorem entry_548_checked : entryAt 548 = entry_548 := by
  rw [entry_chunk_27 2 (by decide)]
  decide +kernel
theorem row_548 : rowAt 548 = data_548 := by
  rw [rowAt, dif_neg (by decide : ¬ 548 < 6), entry_548_checked]
  change forkRow [placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨541, 0, 4, 5⟩ (rowAt 541), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_548
  rw [row_426, row_541, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_548 : EntryGood 548 := by
  unfold EntryGood
  rw [entry_548_checked]
  decide +kernel
theorem good_548 : Good (rowAt 548) := by
  rw [row_548]
  unfold Good
  decide +kernel

theorem entry_549_checked : entryAt 549 = entry_549 := by
  rw [entry_chunk_27 3 (by decide)]
  decide +kernel
theorem row_549 : rowAt 549 = data_549 := by
  rw [rowAt, dif_neg (by decide : ¬ 549 < 6), entry_549_checked]
  change forkRow [placeRow ⟨385, 0, 6, 4⟩ (rowAt 385), placeRow ⟨385, 4, 2, 4⟩ (rowAt 385), placeRow ⟨330, 0, 6, 4⟩ (rowAt 330), placeRow ⟨252, 6, 2, 4⟩ (rowAt 252), placeRow ⟨326, 0, 6, 4⟩ (rowAt 326), placeRow ⟨529, 0, 2, 4⟩ (rowAt 529)] = data_549
  rw [row_385, row_330, row_252, row_326, row_529]
  apply row_ext <;> decide +kernel
theorem entry_good_549 : EntryGood 549 := by
  unfold EntryGood
  rw [entry_549_checked]
  decide +kernel
theorem good_549 : Good (rowAt 549) := by
  rw [row_549]
  unfold Good
  decide +kernel

theorem entry_550_checked : entryAt 550 = entry_550 := by
  rw [entry_chunk_27 4 (by decide)]
  decide +kernel
theorem row_550 : rowAt 550 = data_550 := by
  rw [rowAt, dif_neg (by decide : ¬ 550 < 6), entry_550_checked]
  change forkRow [placeRow ⟨424, 0, 4, 6⟩ (rowAt 424), placeRow ⟨172, 7, 4, 2⟩ (rowAt 172), placeRow ⟨215, 1, 5, 5⟩ (rowAt 215), placeRow ⟨456, 7, 4, 2⟩ (rowAt 456)] = data_550
  rw [row_424, row_172, row_215, row_456]
  apply row_ext <;> decide +kernel
theorem entry_good_550 : EntryGood 550 := by
  unfold EntryGood
  rw [entry_550_checked]
  decide +kernel
theorem good_550 : Good (rowAt 550) := by
  rw [row_550]
  unfold Good
  decide +kernel

theorem entry_551_checked : entryAt 551 = entry_551 := by
  rw [entry_chunk_27 5 (by decide)]
  decide +kernel
theorem row_551 : rowAt 551 = data_551 := by
  rw [rowAt, dif_neg (by decide : ¬ 551 < 6), entry_551_checked]
  change forkRow [placeRow ⟨300, 6, 4, 3⟩ (rowAt 300), placeRow ⟨172, 7, 4, 3⟩ (rowAt 172), placeRow ⟨319, 3, 5, 7⟩ (rowAt 319), placeRow ⟨527, 4, 5, 7⟩ (rowAt 527), placeRow ⟨176, 5, 4, 3⟩ (rowAt 176)] = data_551
  rw [row_300, row_172, row_319, row_527, row_176]
  apply row_ext <;> decide +kernel
theorem entry_good_551 : EntryGood 551 := by
  unfold EntryGood
  rw [entry_551_checked]
  decide +kernel
theorem good_551 : Good (rowAt 551) := by
  rw [row_551]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 548 = data_548 ∧ Good (rowAt 548) ∧ EntryGood 548) ∧ (rowAt 549 = data_549 ∧ Good (rowAt 549) ∧ EntryGood 549) ∧ (rowAt 550 = data_550 ∧ Good (rowAt 550) ∧ EntryGood 550) ∧ (rowAt 551 = data_551 ∧ Good (rowAt 551) ∧ EntryGood 551) ∧ True := by
  exact ⟨⟨row_548, good_548, entry_good_548⟩, ⟨row_549, good_549, entry_good_549⟩, ⟨row_550, good_550, entry_good_550⟩, ⟨row_551, good_551, entry_good_551⟩, trivial⟩
