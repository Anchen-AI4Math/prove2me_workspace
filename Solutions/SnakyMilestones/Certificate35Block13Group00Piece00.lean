import Definitions.Def_Snaky35Cache13
import Solutions.SnakyMilestones.Certificate35Part12
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
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


theorem block13_group00_piece00_correct : (rowAt 416 = data_416 ∧ Good (rowAt 416) ∧ EntryGood 416) ∧ (rowAt 417 = data_417 ∧ Good (rowAt 417) ∧ EntryGood 417) ∧ (rowAt 418 = data_418 ∧ Good (rowAt 418) ∧ EntryGood 418) ∧ (rowAt 419 = data_419 ∧ Good (rowAt 419) ∧ EntryGood 419) ∧ True := by
  exact ⟨⟨row_416, good_416, entry_good_416⟩, ⟨row_417, good_417, entry_good_417⟩, ⟨row_418, good_418, entry_good_418⟩, ⟨row_419, good_419, entry_good_419⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
