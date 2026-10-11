import Definitions.Def_Snaky35Cache13
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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_20 (j : ℕ) (hj : j < 20) : entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_11 : rowAt 11 = data_11 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_29 : rowAt 29 = data_29 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_45 : rowAt 45 = data_45 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_62 : rowAt 62 = data_62 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_68 : rowAt 68 = data_68 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.1).1
theorem row_106 : rowAt 106 = data_106 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_147 : rowAt 147 = data_147 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_164 : rowAt 164 = data_164 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_220 : rowAt 220 = data_220 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_241 : rowAt 241 = data_241 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_243 : rowAt 243 = data_243 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_245 : rowAt 245 = data_245 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_253 : rowAt 253 = data_253 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_270 : rowAt 270 = data_270 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_377 : rowAt 377 = data_377 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_378 : rowAt 378 = data_378 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_385 : rowAt 385 = data_385 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.1).1
theorem row_386 : rowAt 386 = data_386 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.1).1
theorem row_397 : rowAt 397 = data_397 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_402 : rowAt 402 = data_402 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_409 : rowAt 409 = data_409 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_413 : rowAt 413 = data_413 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_415 : rowAt 415 = data_415 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_416_checked : entryAt 416 = entry_416 := by
  rw [entry_chunk_20 10 (by decide)]
  decide +kernel
theorem row_416 : rowAt 416 = data_416 := by
  rw [rowAt, dif_neg (by decide : ¬ 416 < 6), entry_416_checked]
  change forkRow [placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨385, 4, 1, 4⟩ (rowAt 385), placeRow ⟨197, 4, 1, 4⟩ (rowAt 197), placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨245, 2, 5, 4⟩ (rowAt 245), placeRow ⟨220, 2, 5, 4⟩ (rowAt 220)] = data_416
  rw [row_176, row_385, row_197, row_295, row_245, row_220]
  apply row_ext <;> decide +kernel
theorem entry_good_416 : EntryGood 416 := by
  unfold EntryGood
  rw [entry_416_checked]
  decide +kernel
theorem good_416 : Good (rowAt 416) := by
  rw [row_416]
  unfold Good
  decide +kernel

theorem entry_417_checked : entryAt 417 = entry_417 := by
  rw [entry_chunk_20 11 (by decide)]
  decide +kernel
theorem row_417 : rowAt 417 = data_417 := by
  rw [rowAt, dif_neg (by decide : ¬ 417 < 6), entry_417_checked]
  change forkRow [placeRow ⟨409, 0, 2, 4⟩ (rowAt 409), placeRow ⟨11, 1, 4, 2⟩ (rowAt 11), placeRow ⟨270, 4, 4, 2⟩ (rowAt 270)] = data_417
  rw [row_409, row_11, row_270]
  apply row_ext <;> decide +kernel
theorem entry_good_417 : EntryGood 417 := by
  unfold EntryGood
  rw [entry_417_checked]
  decide +kernel
theorem good_417 : Good (rowAt 417) := by
  rw [row_417]
  unfold Good
  decide +kernel

theorem entry_418_checked : entryAt 418 = entry_418 := by
  rw [entry_chunk_20 12 (by decide)]
  decide +kernel
theorem row_418 : rowAt 418 = data_418 := by
  rw [rowAt, dif_neg (by decide : ¬ 418 < 6), entry_418_checked]
  change forkRow [placeRow ⟨68, 4, 1, 3⟩ (rowAt 68), placeRow ⟨62, 6, 1, 3⟩ (rowAt 62), placeRow ⟨147, 6, 1, 3⟩ (rowAt 147), placeRow ⟨413, 0, 4, 2⟩ (rowAt 413)] = data_418
  rw [row_68, row_62, row_147, row_413]
  apply row_ext <;> decide +kernel
theorem entry_good_418 : EntryGood 418 := by
  unfold EntryGood
  rw [entry_418_checked]
  decide +kernel
theorem good_418 : Good (rowAt 418) := by
  rw [row_418]
  unfold Good
  decide +kernel

theorem entry_419_checked : entryAt 419 = entry_419 := by
  rw [entry_chunk_20 13 (by decide)]
  decide +kernel
theorem row_419 : rowAt 419 = data_419 := by
  rw [rowAt, dif_neg (by decide : ¬ 419 < 6), entry_419_checked]
  change forkRow [placeRow ⟨243, 0, 4, 2⟩ (rowAt 243), placeRow ⟨164, 1, 4, 2⟩ (rowAt 164), placeRow ⟨402, 0, 2, 4⟩ (rowAt 402), placeRow ⟨253, 0, 2, 4⟩ (rowAt 253), placeRow ⟨377, 0, 2, 4⟩ (rowAt 377)] = data_419
  rw [row_243, row_164, row_402, row_253, row_377]
  apply row_ext <;> decide +kernel
theorem entry_good_419 : EntryGood 419 := by
  unfold EntryGood
  rw [entry_419_checked]
  decide +kernel
theorem good_419 : Good (rowAt 419) := by
  rw [row_419]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 416 = data_416 ∧ Good (rowAt 416) ∧ EntryGood 416) ∧ (rowAt 417 = data_417 ∧ Good (rowAt 417) ∧ EntryGood 417) ∧ (rowAt 418 = data_418 ∧ Good (rowAt 418) ∧ EntryGood 418) ∧ (rowAt 419 = data_419 ∧ Good (rowAt 419) ∧ EntryGood 419) ∧ True := by
  exact ⟨⟨row_416, good_416, entry_good_416⟩, ⟨row_417, good_417, entry_good_417⟩, ⟨row_418, good_418, entry_good_418⟩, ⟨row_419, good_419, entry_good_419⟩, trivial⟩
