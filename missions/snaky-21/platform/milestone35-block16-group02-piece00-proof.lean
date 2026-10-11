import Definitions.Def_Snaky35Cache16
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_26 (j : ℕ) (hj : j < 20) : entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_217 : rowAt 217 = data_217 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_283 : rowAt 283 = data_283 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_318 : rowAt 318 = data_318 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_321 : rowAt 321 = data_321 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.1).1
theorem row_336 : rowAt 336 = data_336 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_340 : rowAt 340 = data_340 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_359 : rowAt 359 = data_359 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.1).1
theorem row_386 : rowAt 386 = data_386 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.1).1
theorem row_394 : rowAt 394 = data_394 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_401 : rowAt 401 = data_401 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_407 : rowAt 407 = data_407 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_414 : rowAt 414 = data_414 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_423 : rowAt 423 = data_423 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.1).1
theorem row_425 : rowAt 425 = data_425 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_426 : rowAt 426 = data_426 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_434 : rowAt 434 = data_434 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_441 : rowAt 441 = data_441 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_444 : rowAt 444 = data_444 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_453 : rowAt 453 = data_453 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.1).1
theorem row_456 : rowAt 456 = data_456 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.1).1
theorem row_502 : rowAt 502 = data_502 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_504 : rowAt 504 = data_504 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_526 : rowAt 526 = data_526 := (OAI.SnakyCertificate.MilestoneChecks.block16_group01_correct.2.2.2.2.2.2.1).1
theorem entry_528_checked : entryAt 528 = entry_528 := by
  rw [entry_chunk_26 2 (by decide)]
  decide +kernel
theorem row_528 : rowAt 528 = data_528 := by
  rw [rowAt, dif_neg (by decide : ¬ 528 < 6), entry_528_checked]
  change forkRow [placeRow ⟨414, 1, 3, 5⟩ (rowAt 414), placeRow ⟨386, 1, 4, 6⟩ (rowAt 386), placeRow ⟨502, 5, 4, 3⟩ (rowAt 502), placeRow ⟨226, 4, 1, 5⟩ (rowAt 226), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359)] = data_528
  rw [row_414, row_386, row_502, row_226, row_359]
  apply row_ext <;> decide +kernel
theorem entry_good_528 : EntryGood 528 := by
  unfold EntryGood
  rw [entry_528_checked]
  decide +kernel
theorem good_528 : Good (rowAt 528) := by
  rw [row_528]
  unfold Good
  decide +kernel

theorem entry_529_checked : entryAt 529 = entry_529 := by
  rw [entry_chunk_26 3 (by decide)]
  decide +kernel
theorem row_529 : rowAt 529 = data_529 := by
  rw [rowAt, dif_neg (by decide : ¬ 529 < 6), entry_529_checked]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (rowAt 55), placeRow ⟨441, 0, 4, 3⟩ (rowAt 441), placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_529
  rw [row_55, row_441, row_63, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_529 : EntryGood 529 := by
  unfold EntryGood
  rw [entry_529_checked]
  decide +kernel
theorem good_529 : Good (rowAt 529) := by
  rw [row_529]
  unfold Good
  decide +kernel

theorem entry_530_checked : entryAt 530 = entry_530 := by
  rw [entry_chunk_26 4 (by decide)]
  decide +kernel
theorem row_530 : rowAt 530 = data_530 := by
  rw [rowAt, dif_neg (by decide : ¬ 530 < 6), entry_530_checked]
  change forkRow [placeRow ⟨456, 7, 4, 2⟩ (rowAt 456), placeRow ⟨336, 0, 5, 5⟩ (rowAt 336), placeRow ⟨283, 7, 4, 2⟩ (rowAt 283), placeRow ⟨271, 5, 5, 5⟩ (rowAt 271)] = data_530
  rw [row_456, row_336, row_283, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_530 : EntryGood 530 := by
  unfold EntryGood
  rw [entry_530_checked]
  decide +kernel
theorem good_530 : Good (rowAt 530) := by
  rw [row_530]
  unfold Good
  decide +kernel

theorem entry_531_checked : entryAt 531 = entry_531 := by
  rw [entry_chunk_26 5 (by decide)]
  decide +kernel
theorem row_531 : rowAt 531 = data_531 := by
  rw [rowAt, dif_neg (by decide : ¬ 531 < 6), entry_531_checked]
  change forkRow [placeRow ⟨425, 0, 5, 4⟩ (rowAt 425), placeRow ⟨336, 3, 4, 3⟩ (rowAt 336), placeRow ⟨340, 6, 4, 3⟩ (rowAt 340), placeRow ⟨394, 1, 5, 4⟩ (rowAt 394), placeRow ⟨423, 0, 5, 4⟩ (rowAt 423), placeRow ⟨526, 0, 5, 4⟩ (rowAt 526), placeRow ⟨401, 4, 4, 3⟩ (rowAt 401), placeRow ⟨453, 0, 5, 4⟩ (rowAt 453)] = data_531
  rw [row_425, row_336, row_340, row_394, row_423, row_526, row_401, row_453]
  apply row_ext <;> decide +kernel
theorem entry_good_531 : EntryGood 531 := by
  unfold EntryGood
  rw [entry_531_checked]
  decide +kernel
theorem good_531 : Good (rowAt 531) := by
  rw [row_531]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 528 = data_528 ∧ Good (rowAt 528) ∧ EntryGood 528) ∧ (rowAt 529 = data_529 ∧ Good (rowAt 529) ∧ EntryGood 529) ∧ (rowAt 530 = data_530 ∧ Good (rowAt 530) ∧ EntryGood 530) ∧ (rowAt 531 = data_531 ∧ Good (rowAt 531) ∧ EntryGood 531) ∧ True := by
  exact ⟨⟨row_528, good_528, entry_good_528⟩, ⟨row_529, good_529, entry_good_529⟩, ⟨row_530, good_530, entry_good_530⟩, ⟨row_531, good_531, entry_good_531⟩, trivial⟩
