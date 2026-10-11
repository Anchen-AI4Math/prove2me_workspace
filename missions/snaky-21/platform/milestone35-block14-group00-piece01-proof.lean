import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group00_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_22 (j : ℕ) (hj : j < 20) : entryAt (446 + j) = tableChunk_22[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_20 : rowAt 20 = data_20 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_39 : rowAt 39 = data_39 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.1).1
theorem row_58 : rowAt 58 = data_58 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_118 : rowAt 118 = data_118 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_244 : rowAt 244 = data_244 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_307 : rowAt 307 = data_307 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_359 : rowAt 359 = data_359 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.1).1
theorem row_386 : rowAt 386 = data_386 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.1).1
theorem row_389 : rowAt 389 = data_389 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.1).1
theorem row_414 : rowAt 414 = data_414 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_436 : rowAt 436 = data_436 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_439 : rowAt 439 = data_439 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_440 : rowAt 440 = data_440 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_451 : rowAt 451 = data_451 := (OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece00_correct.2.2.2.1).1
theorem entry_452_checked : entryAt 452 = entry_452 := by
  rw [entry_chunk_22 6 (by decide)]
  decide +kernel
theorem row_452 : rowAt 452 = data_452 := by
  rw [rowAt, dif_neg (by decide : ¬ 452 < 6), entry_452_checked]
  change forkRow [placeRow ⟨24, 1, 5, 7⟩ (rowAt 24), placeRow ⟨451, 0, 3, 8⟩ (rowAt 451), placeRow ⟨25, 3, 3, 7⟩ (rowAt 25)] = data_452
  rw [row_24, row_451, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_452 : EntryGood 452 := by
  unfold EntryGood
  rw [entry_452_checked]
  decide +kernel
theorem good_452 : Good (rowAt 452) := by
  rw [row_452]
  unfold Good
  decide +kernel

theorem entry_453_checked : entryAt 453 = entry_453 := by
  rw [entry_chunk_22 7 (by decide)]
  decide +kernel
theorem row_453 : rowAt 453 = data_453 := by
  rw [rowAt, dif_neg (by decide : ¬ 453 < 6), entry_453_checked]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (rowAt 359), placeRow ⟨226, 7, 3, 1⟩ (rowAt 226), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386), placeRow ⟨389, 1, 5, 4⟩ (rowAt 389), placeRow ⟨414, 4, 3, 3⟩ (rowAt 414)] = data_453
  rw [row_359, row_226, row_386, row_389, row_414]
  apply row_ext <;> decide +kernel
theorem entry_good_453 : EntryGood 453 := by
  unfold EntryGood
  rw [entry_453_checked]
  decide +kernel
theorem good_453 : Good (rowAt 453) := by
  rw [row_453]
  unfold Good
  decide +kernel

theorem entry_454_checked : entryAt 454 = entry_454 := by
  rw [entry_chunk_22 8 (by decide)]
  decide +kernel
theorem row_454 : rowAt 454 = data_454 := by
  rw [rowAt, dif_neg (by decide : ¬ 454 < 6), entry_454_checked]
  change forkRow [placeRow ⟨58, 0, 6, 3⟩ (rowAt 58), placeRow ⟨436, 0, 3, 6⟩ (rowAt 436)] = data_454
  rw [row_58, row_436]
  apply row_ext <;> decide +kernel
theorem entry_good_454 : EntryGood 454 := by
  unfold EntryGood
  rw [entry_454_checked]
  decide +kernel
theorem good_454 : Good (rowAt 454) := by
  rw [row_454]
  unfold Good
  decide +kernel

theorem entry_455_checked : entryAt 455 = entry_455 := by
  rw [entry_chunk_22 9 (by decide)]
  decide +kernel
theorem row_455 : rowAt 455 = data_455 := by
  rw [rowAt, dif_neg (by decide : ¬ 455 < 6), entry_455_checked]
  change forkRow [placeRow ⟨20, 2, 4, 5⟩ (rowAt 20), placeRow ⟨118, 3, 0, 5⟩ (rowAt 118), placeRow ⟨39, 2, 3, 4⟩ (rowAt 39)] = data_455
  rw [row_20, row_118, row_39]
  apply row_ext <;> decide +kernel
theorem entry_good_455 : EntryGood 455 := by
  unfold EntryGood
  rw [entry_455_checked]
  decide +kernel
theorem good_455 : Good (rowAt 455) := by
  rw [row_455]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 452 = data_452 ∧ Good (rowAt 452) ∧ EntryGood 452) ∧ (rowAt 453 = data_453 ∧ Good (rowAt 453) ∧ EntryGood 453) ∧ (rowAt 454 = data_454 ∧ Good (rowAt 454) ∧ EntryGood 454) ∧ (rowAt 455 = data_455 ∧ Good (rowAt 455) ∧ EntryGood 455) ∧ True := by
  exact ⟨⟨row_452, good_452, entry_good_452⟩, ⟨row_453, good_453, entry_good_453⟩, ⟨row_454, good_454, entry_good_454⟩, ⟨row_455, good_455, entry_good_455⟩, trivial⟩
