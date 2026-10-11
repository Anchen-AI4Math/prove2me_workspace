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
theorem entry_532_checked : entryAt 532 = entry_532 := by
  rw [entry_chunk_26 6 (by decide)]
  decide +kernel
theorem row_532 : rowAt 532 = data_532 := by
  rw [rowAt, dif_neg (by decide : ¬ 532 < 6), entry_532_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨6, 7, 3, 0⟩ (rowAt 6)] = data_532
  rw [row_504, row_6]
  apply row_ext <;> decide +kernel
theorem entry_good_532 : EntryGood 532 := by
  unfold EntryGood
  rw [entry_532_checked]
  decide +kernel
theorem good_532 : Good (rowAt 532) := by
  rw [row_532]
  unfold Good
  decide +kernel

theorem entry_533_checked : entryAt 533 = entry_533 := by
  rw [entry_chunk_26 7 (by decide)]
  decide +kernel
theorem row_533 : rowAt 533 = data_533 := by
  rw [rowAt, dif_neg (by decide : ¬ 533 < 6), entry_533_checked]
  change forkRow [placeRow ⟨318, 4, 4, 5⟩ (rowAt 318), placeRow ⟨319, 7, 5, 1⟩ (rowAt 319), placeRow ⟨407, 4, 4, 1⟩ (rowAt 407), placeRow ⟨173, 3, 4, 5⟩ (rowAt 173), placeRow ⟨217, 1, 4, 5⟩ (rowAt 217)] = data_533
  rw [row_318, row_319, row_407, row_173, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_533 : EntryGood 533 := by
  unfold EntryGood
  rw [entry_533_checked]
  decide +kernel
theorem good_533 : Good (rowAt 533) := by
  rw [row_533]
  unfold Good
  decide +kernel

theorem entry_534_checked : entryAt 534 = entry_534 := by
  rw [entry_chunk_26 8 (by decide)]
  decide +kernel
theorem row_534 : rowAt 534 = data_534 := by
  rw [rowAt, dif_neg (by decide : ¬ 534 < 6), entry_534_checked]
  change forkRow [placeRow ⟨434, 0, 4, 6⟩ (rowAt 434), placeRow ⟨12, 6, 1, 3⟩ (rowAt 12)] = data_534
  rw [row_434, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_534 : EntryGood 534 := by
  unfold EntryGood
  rw [entry_534_checked]
  decide +kernel
theorem good_534 : Good (rowAt 534) := by
  rw [row_534]
  unfold Good
  decide +kernel

theorem entry_535_checked : entryAt 535 = entry_535 := by
  rw [entry_chunk_26 9 (by decide)]
  decide +kernel
theorem row_535 : rowAt 535 = data_535 := by
  rw [rowAt, dif_neg (by decide : ¬ 535 < 6), entry_535_checked]
  change forkRow [placeRow ⟨444, 0, 4, 5⟩ (rowAt 444), placeRow ⟨426, 0, 4, 5⟩ (rowAt 426), placeRow ⟨25, 0, 5, 4⟩ (rowAt 25), placeRow ⟨321, 4, 4, 2⟩ (rowAt 321)] = data_535
  rw [row_444, row_426, row_25, row_321]
  apply row_ext <;> decide +kernel
theorem entry_good_535 : EntryGood 535 := by
  unfold EntryGood
  rw [entry_535_checked]
  decide +kernel
theorem good_535 : Good (rowAt 535) := by
  rw [row_535]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 532 = data_532 ∧ Good (rowAt 532) ∧ EntryGood 532) ∧ (rowAt 533 = data_533 ∧ Good (rowAt 533) ∧ EntryGood 533) ∧ (rowAt 534 = data_534 ∧ Good (rowAt 534) ∧ EntryGood 534) ∧ (rowAt 535 = data_535 ∧ Good (rowAt 535) ∧ EntryGood 535) ∧ True := by
  exact ⟨⟨row_532, good_532, entry_good_532⟩, ⟨row_533, good_533, entry_good_533⟩, ⟨row_534, good_534, entry_good_534⟩, ⟨row_535, good_535, entry_good_535⟩, trivial⟩
