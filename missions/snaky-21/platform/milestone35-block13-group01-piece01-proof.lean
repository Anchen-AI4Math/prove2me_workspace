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
theorem entry_428_checked : entryAt 428 = entry_428 := by
  rw [entry_chunk_21 2 (by decide)]
  decide +kernel
theorem row_428 : rowAt 428 = data_428 := by
  rw [rowAt, dif_neg (by decide : ¬ 428 < 6), entry_428_checked]
  change forkRow [placeRow ⟨26, 3, 4, 3⟩ (rowAt 26), placeRow ⟨416, 0, 5, 4⟩ (rowAt 416), placeRow ⟨244, 0, 5, 4⟩ (rowAt 244), placeRow ⟨329, 0, 4, 3⟩ (rowAt 329)] = data_428
  rw [row_26, row_416, row_244, row_329]
  apply row_ext <;> decide +kernel
theorem entry_good_428 : EntryGood 428 := by
  unfold EntryGood
  rw [entry_428_checked]
  decide +kernel
theorem good_428 : Good (rowAt 428) := by
  rw [row_428]
  unfold Good
  decide +kernel

theorem entry_429_checked : entryAt 429 = entry_429 := by
  rw [entry_chunk_21 3 (by decide)]
  decide +kernel
theorem row_429 : rowAt 429 = data_429 := by
  rw [rowAt, dif_neg (by decide : ¬ 429 < 6), entry_429_checked]
  change forkRow [placeRow ⟨128, 0, 6, 3⟩ (rowAt 128), placeRow ⟨28, 3, 4, 5⟩ (rowAt 28)] = data_429
  rw [row_128, row_28]
  apply row_ext <;> decide +kernel
theorem entry_good_429 : EntryGood 429 := by
  unfold EntryGood
  rw [entry_429_checked]
  decide +kernel
theorem good_429 : Good (rowAt 429) := by
  rw [row_429]
  unfold Good
  decide +kernel

theorem entry_430_checked : entryAt 430 = entry_430 := by
  rw [entry_chunk_21 4 (by decide)]
  decide +kernel
theorem row_430 : rowAt 430 = data_430 := by
  rw [rowAt, dif_neg (by decide : ¬ 430 < 6), entry_430_checked]
  change forkRow [placeRow ⟨277, 7, 1, 3⟩ (rowAt 277), placeRow ⟨338, 4, 3, 4⟩ (rowAt 338), placeRow ⟨336, 1, 4, 3⟩ (rowAt 336), placeRow ⟨375, 2, 4, 3⟩ (rowAt 375), placeRow ⟨277, 6, 3, 1⟩ (rowAt 277)] = data_430
  rw [row_277, row_338, row_336, row_375]
  apply row_ext <;> decide +kernel
theorem entry_good_430 : EntryGood 430 := by
  unfold EntryGood
  rw [entry_430_checked]
  decide +kernel
theorem good_430 : Good (rowAt 430) := by
  rw [row_430]
  unfold Good
  decide +kernel

theorem entry_431_checked : entryAt 431 = entry_431 := by
  rw [entry_chunk_21 5 (by decide)]
  decide +kernel
theorem row_431 : rowAt 431 = data_431 := by
  rw [rowAt, dif_neg (by decide : ¬ 431 < 6), entry_431_checked]
  change forkRow [placeRow ⟨73, 4, 3, 3⟩ (rowAt 73), placeRow ⟨302, 1, 5, 2⟩ (rowAt 302), placeRow ⟨415, 0, 6, 4⟩ (rowAt 415), placeRow ⟨398, 0, 6, 4⟩ (rowAt 398)] = data_431
  rw [row_73, row_302, row_415, row_398]
  apply row_ext <;> decide +kernel
theorem entry_good_431 : EntryGood 431 := by
  unfold EntryGood
  rw [entry_431_checked]
  decide +kernel
theorem good_431 : Good (rowAt 431) := by
  rw [row_431]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 428 = data_428 ∧ Good (rowAt 428) ∧ EntryGood 428) ∧ (rowAt 429 = data_429 ∧ Good (rowAt 429) ∧ EntryGood 429) ∧ (rowAt 430 = data_430 ∧ Good (rowAt 430) ∧ EntryGood 430) ∧ (rowAt 431 = data_431 ∧ Good (rowAt 431) ∧ EntryGood 431) ∧ True := by
  exact ⟨⟨row_428, good_428, entry_good_428⟩, ⟨row_429, good_429, entry_good_429⟩, ⟨row_430, good_430, entry_good_430⟩, ⟨row_431, good_431, entry_good_431⟩, trivial⟩
