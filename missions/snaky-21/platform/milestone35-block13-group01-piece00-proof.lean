import Definitions.Def_Snaky35Cache13
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_20 (j : ℕ) (hj : j < 20) : entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_21 (j : ℕ) (hj : j < 20) : entryAt (426 + j) = tableChunk_21[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_26 : rowAt 26 = data_26 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_28 : rowAt 28 = data_28 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_45 : rowAt 45 = data_45 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_73 : rowAt 73 = data_73 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_106 : rowAt 106 = data_106 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_128 : rowAt 128 = data_128 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.1).1
theorem row_216 : rowAt 216 = data_216 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_244 : rowAt 244 = data_244 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_277 : rowAt 277 = data_277 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_291 : rowAt 291 = data_291 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_302 : rowAt 302 = data_302 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_328 : rowAt 328 = data_328 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.1).1
theorem row_329 : rowAt 329 = data_329 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_336 : rowAt 336 = data_336 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_338 : rowAt 338 = data_338 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_375 : rowAt 375 = data_375 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_378 : rowAt 378 = data_378 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_386 : rowAt 386 = data_386 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.1).1
theorem row_394 : rowAt 394 = data_394 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_397 : rowAt 397 = data_397 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_398 : rowAt 398 = data_398 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_415 : rowAt 415 = data_415 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_416 : rowAt 416 = data_416 := (OAI.SnakyCertificate.MilestoneChecks.block13_group00_correct.1).1
theorem row_420 : rowAt 420 = data_420 := (OAI.SnakyCertificate.MilestoneChecks.block13_group00_correct.2.2.2.2.1).1
theorem entry_424_checked : entryAt 424 = entry_424 := by
  rw [entry_chunk_20 18 (by decide)]
  decide +kernel
theorem row_424 : rowAt 424 = data_424 := by
  rw [rowAt, dif_neg (by decide : ¬ 424 < 6), entry_424_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨394, 0, 6, 4⟩ (rowAt 394), placeRow ⟨216, 3, 4, 5⟩ (rowAt 216)] = data_424
  rw [row_55, row_394, row_216]
  apply row_ext <;> decide +kernel
theorem entry_good_424 : EntryGood 424 := by
  unfold EntryGood
  rw [entry_424_checked]
  decide +kernel
theorem good_424 : Good (rowAt 424) := by
  rw [row_424]
  unfold Good
  decide +kernel

theorem entry_425_checked : entryAt 425 = entry_425 := by
  rw [entry_chunk_20 19 (by decide)]
  decide +kernel
theorem row_425 : rowAt 425 = data_425 := by
  rw [rowAt, dif_neg (by decide : ¬ 425 < 6), entry_425_checked]
  change forkRow [placeRow ⟨386, 0, 5, 4⟩ (rowAt 386), placeRow ⟨226, 1, 4, 5⟩ (rowAt 226), placeRow ⟨378, 4, 2, 4⟩ (rowAt 378), placeRow ⟨378, 0, 5, 4⟩ (rowAt 378), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386)] = data_425
  rw [row_386, row_226, row_378]
  apply row_ext <;> decide +kernel
theorem entry_good_425 : EntryGood 425 := by
  unfold EntryGood
  rw [entry_425_checked]
  decide +kernel
theorem good_425 : Good (rowAt 425) := by
  rw [row_425]
  unfold Good
  decide +kernel

theorem entry_426_checked : entryAt 426 = entry_426 := by
  rw [entry_chunk_21 0 (by decide)]
  decide +kernel
theorem row_426 : rowAt 426 = data_426 := by
  rw [rowAt, dif_neg (by decide : ¬ 426 < 6), entry_426_checked]
  change forkRow [placeRow ⟨300, 6, 4, 1⟩ (rowAt 300), placeRow ⟨252, 1, 4, 5⟩ (rowAt 252), placeRow ⟨397, 0, 3, 4⟩ (rowAt 397), placeRow ⟨291, 1, 4, 1⟩ (rowAt 291), placeRow ⟨328, 0, 4, 5⟩ (rowAt 328), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319)] = data_426
  rw [row_300, row_252, row_397, row_291, row_328, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_426 : EntryGood 426 := by
  unfold EntryGood
  rw [entry_426_checked]
  decide +kernel
theorem good_426 : Good (rowAt 426) := by
  rw [row_426]
  unfold Good
  decide +kernel

theorem entry_427_checked : entryAt 427 = entry_427 := by
  rw [entry_chunk_21 1 (by decide)]
  decide +kernel
theorem row_427 : rowAt 427 = data_427 := by
  rw [rowAt, dif_neg (by decide : ¬ 427 < 6), entry_427_checked]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (rowAt 45), placeRow ⟨106, 6, 2, 3⟩ (rowAt 106), placeRow ⟨420, 1, 6, 4⟩ (rowAt 420)] = data_427
  rw [row_45, row_106, row_420]
  apply row_ext <;> decide +kernel
theorem entry_good_427 : EntryGood 427 := by
  unfold EntryGood
  rw [entry_427_checked]
  decide +kernel
theorem good_427 : Good (rowAt 427) := by
  rw [row_427]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 424 = data_424 ∧ Good (rowAt 424) ∧ EntryGood 424) ∧ (rowAt 425 = data_425 ∧ Good (rowAt 425) ∧ EntryGood 425) ∧ (rowAt 426 = data_426 ∧ Good (rowAt 426) ∧ EntryGood 426) ∧ (rowAt 427 = data_427 ∧ Good (rowAt 427) ∧ EntryGood 427) ∧ True := by
  exact ⟨⟨row_424, good_424, entry_good_424⟩, ⟨row_425, good_425, entry_good_425⟩, ⟨row_426, good_426, entry_good_426⟩, ⟨row_427, good_427, entry_good_427⟩, trivial⟩
