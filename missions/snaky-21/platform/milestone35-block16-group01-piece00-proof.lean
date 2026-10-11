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
theorem entry_520_checked : entryAt 520 = entry_520 := by
  rw [entry_chunk_25 14 (by decide)]
  decide +kernel
theorem row_520 : rowAt 520 = data_520 := by
  rw [rowAt, dif_neg (by decide : ¬ 520 < 6), entry_520_checked]
  change forkRow [placeRow ⟨254, 0, 2, 3⟩ (rowAt 254), placeRow ⟨200, 5, 6, 4⟩ (rowAt 200), placeRow ⟨271, 6, 5, 3⟩ (rowAt 271), placeRow ⟨215, 2, 5, 3⟩ (rowAt 215), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252)] = data_520
  rw [row_254, row_200, row_271, row_215, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_520 : EntryGood 520 := by
  unfold EntryGood
  rw [entry_520_checked]
  decide +kernel
theorem good_520 : Good (rowAt 520) := by
  rw [row_520]
  unfold Good
  decide +kernel

theorem entry_521_checked : entryAt 521 = entry_521 := by
  rw [entry_chunk_25 15 (by decide)]
  decide +kernel
theorem row_521 : rowAt 521 = data_521 := by
  rw [rowAt, dif_neg (by decide : ¬ 521 < 6), entry_521_checked]
  change forkRow [placeRow ⟨492, 4, 5, 1⟩ (rowAt 492), placeRow ⟨2, 7, 4, 2⟩ (rowAt 2)] = data_521
  rw [row_492, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_521 : EntryGood 521 := by
  unfold EntryGood
  rw [entry_521_checked]
  decide +kernel
theorem good_521 : Good (rowAt 521) := by
  rw [row_521]
  unfold Good
  decide +kernel

theorem entry_522_checked : entryAt 522 = entry_522 := by
  rw [entry_chunk_25 16 (by decide)]
  decide +kernel
theorem row_522 : rowAt 522 = data_522 := by
  rw [rowAt, dif_neg (by decide : ¬ 522 < 6), entry_522_checked]
  change forkRow [placeRow ⟨176, 3, 4, 6⟩ (rowAt 176), placeRow ⟨338, 2, 3, 3⟩ (rowAt 338), placeRow ⟨252, 1, 4, 6⟩ (rowAt 252)] = data_522
  rw [row_176, row_338, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_522 : EntryGood 522 := by
  unfold EntryGood
  rw [entry_522_checked]
  decide +kernel
theorem good_522 : Good (rowAt 522) := by
  rw [row_522]
  unfold Good
  decide +kernel

theorem entry_523_checked : entryAt 523 = entry_523 := by
  rw [entry_chunk_25 17 (by decide)]
  decide +kernel
theorem row_523 : rowAt 523 = data_523 := by
  rw [rowAt, dif_neg (by decide : ¬ 523 < 6), entry_523_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨511, 4, 1, 6⟩ (rowAt 511)] = data_523
  rw [row_303, row_25, row_107, row_511]
  apply row_ext <;> decide +kernel
theorem entry_good_523 : EntryGood 523 := by
  unfold EntryGood
  rw [entry_523_checked]
  decide +kernel
theorem good_523 : Good (rowAt 523) := by
  rw [row_523]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 520 = data_520 ∧ Good (rowAt 520) ∧ EntryGood 520) ∧ (rowAt 521 = data_521 ∧ Good (rowAt 521) ∧ EntryGood 521) ∧ (rowAt 522 = data_522 ∧ Good (rowAt 522) ∧ EntryGood 522) ∧ (rowAt 523 = data_523 ∧ Good (rowAt 523) ∧ EntryGood 523) ∧ True := by
  exact ⟨⟨row_520, good_520, entry_good_520⟩, ⟨row_521, good_521, entry_good_521⟩, ⟨row_522, good_522, entry_good_522⟩, ⟨row_523, good_523, entry_good_523⟩, trivial⟩
