import Definitions.Def_Snaky35Cache16
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_25 (j : ℕ) (hj : j < 20) : entryAt (506 + j) = tableChunk_25[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_26 (j : ℕ) (hj : j < 20) : entryAt (526 + j) = tableChunk_26[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_38 : rowAt 38 = data_38 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_200 : rowAt 200 = data_200 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_254 : rowAt 254 = data_254 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_303 : rowAt 303 = data_303 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_327 : rowAt 327 = data_327 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.1).1
theorem row_338 : rowAt 338 = data_338 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_359 : rowAt 359 = data_359 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.1).1
theorem row_387 : rowAt 387 = data_387 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.1).1
theorem row_399 : rowAt 399 = data_399 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_416 : rowAt 416 = data_416 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.1).1
theorem row_430 : rowAt 430 = data_430 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_489 : rowAt 489 = data_489 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_491 : rowAt 491 = data_491 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_492 : rowAt 492 = data_492 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_504 : rowAt 504 = data_504 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_511 : rowAt 511 = data_511 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_519 : rowAt 519 = data_519 := (OAI.SnakyCertificate.MilestoneChecks.block16_group00_correct.2.2.2.2.2.2.2.1).1
theorem entry_524_checked : entryAt 524 = entry_524 := by
  rw [entry_chunk_25 18 (by decide)]
  decide +kernel
theorem row_524 : rowAt 524 = data_524 := by
  rw [rowAt, dif_neg (by decide : ¬ 524 < 6), entry_524_checked]
  change forkRow [placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨261, 0, 3, 4⟩ (rowAt 261)] = data_524
  rw [row_504, row_180, row_261]
  apply row_ext <;> decide +kernel
theorem entry_good_524 : EntryGood 524 := by
  unfold EntryGood
  rw [entry_524_checked]
  decide +kernel
theorem good_524 : Good (rowAt 524) := by
  rw [row_524]
  unfold Good
  decide +kernel

theorem entry_525_checked : entryAt 525 = entry_525 := by
  rw [entry_chunk_25 19 (by decide)]
  decide +kernel
theorem row_525 : rowAt 525 = data_525 := by
  rw [rowAt, dif_neg (by decide : ¬ 525 < 6), entry_525_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨430, 0, 4, 6⟩ (rowAt 430), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107)] = data_525
  rw [row_303, row_25, row_430, row_107]
  apply row_ext <;> decide +kernel
theorem entry_good_525 : EntryGood 525 := by
  unfold EntryGood
  rw [entry_525_checked]
  decide +kernel
theorem good_525 : Good (rowAt 525) := by
  rw [row_525]
  unfold Good
  decide +kernel

theorem entry_526_checked : entryAt 526 = entry_526 := by
  rw [entry_chunk_26 0 (by decide)]
  decide +kernel
theorem row_526 : rowAt 526 = data_526 := by
  rw [rowAt, dif_neg (by decide : ¬ 526 < 6), entry_526_checked]
  change forkRow [placeRow ⟨359, 0, 4, 3⟩ (rowAt 359), placeRow ⟨416, 4, 2, 4⟩ (rowAt 416), placeRow ⟨327, 5, 4, 3⟩ (rowAt 327), placeRow ⟨489, 0, 5, 4⟩ (rowAt 489), placeRow ⟨399, 3, 2, 4⟩ (rowAt 399)] = data_526
  rw [row_359, row_416, row_327, row_489, row_399]
  apply row_ext <;> decide +kernel
theorem entry_good_526 : EntryGood 526 := by
  unfold EntryGood
  rw [entry_526_checked]
  decide +kernel
theorem good_526 : Good (rowAt 526) := by
  rw [row_526]
  unfold Good
  decide +kernel

theorem entry_527_checked : entryAt 527 = entry_527 := by
  rw [entry_chunk_26 1 (by decide)]
  decide +kernel
theorem row_527 : rowAt 527 = data_527 := by
  rw [rowAt, dif_neg (by decide : ¬ 527 < 6), entry_527_checked]
  change forkRow [placeRow ⟨387, 4, 4, 3⟩ (rowAt 387), placeRow ⟨38, 3, 4, 5⟩ (rowAt 38), placeRow ⟨491, 0, 5, 4⟩ (rowAt 491), placeRow ⟨519, 0, 6, 4⟩ (rowAt 519)] = data_527
  rw [row_387, row_38, row_491, row_519]
  apply row_ext <;> decide +kernel
theorem entry_good_527 : EntryGood 527 := by
  unfold EntryGood
  rw [entry_527_checked]
  decide +kernel
theorem good_527 : Good (rowAt 527) := by
  rw [row_527]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 524 = data_524 ∧ Good (rowAt 524) ∧ EntryGood 524) ∧ (rowAt 525 = data_525 ∧ Good (rowAt 525) ∧ EntryGood 525) ∧ (rowAt 526 = data_526 ∧ Good (rowAt 526) ∧ EntryGood 526) ∧ (rowAt 527 = data_527 ∧ Good (rowAt 527) ∧ EntryGood 527) ∧ True := by
  exact ⟨⟨row_524, good_524, entry_good_524⟩, ⟨row_525, good_525, entry_good_525⟩, ⟨row_526, good_526, entry_good_526⟩, ⟨row_527, good_527, entry_good_527⟩, trivial⟩
