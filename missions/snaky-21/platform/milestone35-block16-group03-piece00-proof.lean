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
theorem entry_536_checked : entryAt 536 = entry_536 := by
  rw [entry_chunk_26 10 (by decide)]
  decide +kernel
theorem row_536 : rowAt 536 = data_536 := by
  rw [rowAt, dif_neg (by decide : ¬ 536 < 6), entry_536_checked]
  change forkRow [placeRow ⟨307, 0, 4, 3⟩ (rowAt 307), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨534, 0, 5, 2⟩ (rowAt 534)] = data_536
  rw [row_307, row_244, row_26, row_534]
  apply row_ext <;> decide +kernel
theorem entry_good_536 : EntryGood 536 := by
  unfold EntryGood
  rw [entry_536_checked]
  decide +kernel
theorem good_536 : Good (rowAt 536) := by
  rw [row_536]
  unfold Good
  decide +kernel

theorem entry_537_checked : entryAt 537 = entry_537 := by
  rw [entry_chunk_26 11 (by decide)]
  decide +kernel
theorem row_537 : rowAt 537 = data_537 := by
  rw [rowAt, dif_neg (by decide : ¬ 537 < 6), entry_537_checked]
  change forkRow [placeRow ⟨373, 2, 2, 4⟩ (rowAt 373), placeRow ⟨271, 3, 3, 3⟩ (rowAt 271), placeRow ⟨176, 1, 4, 6⟩ (rowAt 176), placeRow ⟨330, 1, 4, 6⟩ (rowAt 330)] = data_537
  rw [row_373, row_271, row_176, row_330]
  apply row_ext <;> decide +kernel
theorem entry_good_537 : EntryGood 537 := by
  unfold EntryGood
  rw [entry_537_checked]
  decide +kernel
theorem good_537 : Good (rowAt 537) := by
  rw [row_537]
  unfold Good
  decide +kernel

theorem entry_538_checked : entryAt 538 = entry_538 := by
  rw [entry_chunk_26 12 (by decide)]
  decide +kernel
theorem row_538 : rowAt 538 = data_538 := by
  rw [rowAt, dif_neg (by decide : ¬ 538 < 6), entry_538_checked]
  change forkRow [placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨470, 0, 4, 5⟩ (rowAt 470), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64), placeRow ⟨55, 4, 3, 4⟩ (rowAt 55)] = data_538
  rw [row_63, row_470, row_64, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_538 : EntryGood 538 := by
  unfold EntryGood
  rw [entry_538_checked]
  decide +kernel
theorem good_538 : Good (rowAt 538) := by
  rw [row_538]
  unfold Good
  decide +kernel

theorem entry_539_checked : entryAt 539 = entry_539 := by
  rw [entry_chunk_26 13 (by decide)]
  decide +kernel
theorem row_539 : rowAt 539 = data_539 := by
  rw [rowAt, dif_neg (by decide : ¬ 539 < 6), entry_539_checked]
  change forkRow [placeRow ⟨51, 1, 5, 4⟩ (rowAt 51), placeRow ⟨488, 3, 4, 3⟩ (rowAt 488), placeRow ⟨428, 0, 5, 4⟩ (rowAt 428), placeRow ⟨516, 0, 5, 4⟩ (rowAt 516)] = data_539
  rw [row_51, row_488, row_428, row_516]
  apply row_ext <;> decide +kernel
theorem entry_good_539 : EntryGood 539 := by
  unfold EntryGood
  rw [entry_539_checked]
  decide +kernel
theorem good_539 : Good (rowAt 539) := by
  rw [row_539]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 536 = data_536 ∧ Good (rowAt 536) ∧ EntryGood 536) ∧ (rowAt 537 = data_537 ∧ Good (rowAt 537) ∧ EntryGood 537) ∧ (rowAt 538 = data_538 ∧ Good (rowAt 538) ∧ EntryGood 538) ∧ (rowAt 539 = data_539 ∧ Good (rowAt 539) ∧ EntryGood 539) ∧ True := by
  exact ⟨⟨row_536, good_536, entry_good_536⟩, ⟨row_537, good_537, entry_good_537⟩, ⟨row_538, good_538, entry_good_538⟩, ⟨row_539, good_539, entry_good_539⟩, trivial⟩
