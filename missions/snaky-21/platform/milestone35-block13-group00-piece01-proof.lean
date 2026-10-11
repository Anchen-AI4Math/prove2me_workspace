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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group00_piece00_correct
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
theorem row_419 : rowAt 419 = data_419 := (OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece00_correct.2.2.2.1).1
theorem entry_420_checked : entryAt 420 = entry_420 := by
  rw [entry_chunk_20 14 (by decide)]
  decide +kernel
theorem row_420 : rowAt 420 = data_420 := by
  rw [rowAt, dif_neg (by decide : ¬ 420 < 6), entry_420_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨415, 0, 6, 4⟩ (rowAt 415)] = data_420
  rw [row_29, row_415]
  apply row_ext <;> decide +kernel
theorem entry_good_420 : EntryGood 420 := by
  unfold EntryGood
  rw [entry_420_checked]
  decide +kernel
theorem good_420 : Good (rowAt 420) := by
  rw [row_420]
  unfold Good
  decide +kernel

theorem entry_421_checked : entryAt 421 = entry_421 := by
  rw [entry_chunk_20 15 (by decide)]
  decide +kernel
theorem row_421 : rowAt 421 = data_421 := by
  rw [rowAt, dif_neg (by decide : ¬ 421 < 6), entry_421_checked]
  change forkRow [placeRow ⟨24, 6, 2, 3⟩ (rowAt 24), placeRow ⟨397, 1, 5, 3⟩ (rowAt 397), placeRow ⟨25, 6, 2, 3⟩ (rowAt 25), placeRow ⟨241, 4, 2, 4⟩ (rowAt 241)] = data_421
  rw [row_24, row_397, row_25, row_241]
  apply row_ext <;> decide +kernel
theorem entry_good_421 : EntryGood 421 := by
  unfold EntryGood
  rw [entry_421_checked]
  decide +kernel
theorem good_421 : Good (rowAt 421) := by
  rw [row_421]
  unfold Good
  decide +kernel

theorem entry_422_checked : entryAt 422 = entry_422 := by
  rw [entry_chunk_20 16 (by decide)]
  decide +kernel
theorem row_422 : rowAt 422 = data_422 := by
  rw [rowAt, dif_neg (by decide : ¬ 422 < 6), entry_422_checked]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (rowAt 45), placeRow ⟨106, 6, 2, 3⟩ (rowAt 106), placeRow ⟨419, 1, 6, 6⟩ (rowAt 419)] = data_422
  rw [row_45, row_106, row_419]
  apply row_ext <;> decide +kernel
theorem entry_good_422 : EntryGood 422 := by
  unfold EntryGood
  rw [entry_422_checked]
  decide +kernel
theorem good_422 : Good (rowAt 422) := by
  rw [row_422]
  unfold Good
  decide +kernel

theorem entry_423_checked : entryAt 423 = entry_423 := by
  rw [entry_chunk_20 17 (by decide)]
  decide +kernel
theorem row_423 : rowAt 423 = data_423 := by
  rw [rowAt, dif_neg (by decide : ¬ 423 < 6), entry_423_checked]
  change forkRow [placeRow ⟨378, 4, 2, 4⟩ (rowAt 378), placeRow ⟨386, 0, 5, 4⟩ (rowAt 386), placeRow ⟨226, 3, 3, 5⟩ (rowAt 226), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386), placeRow ⟨378, 0, 5, 4⟩ (rowAt 378)] = data_423
  rw [row_378, row_386, row_226]
  apply row_ext <;> decide +kernel
theorem entry_good_423 : EntryGood 423 := by
  unfold EntryGood
  rw [entry_423_checked]
  decide +kernel
theorem good_423 : Good (rowAt 423) := by
  rw [row_423]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 420 = data_420 ∧ Good (rowAt 420) ∧ EntryGood 420) ∧ (rowAt 421 = data_421 ∧ Good (rowAt 421) ∧ EntryGood 421) ∧ (rowAt 422 = data_422 ∧ Good (rowAt 422) ∧ EntryGood 422) ∧ (rowAt 423 = data_423 ∧ Good (rowAt 423) ∧ EntryGood 423) ∧ True := by
  exact ⟨⟨row_420, good_420, entry_good_420⟩, ⟨row_421, good_421, entry_good_421⟩, ⟨row_422, good_422, entry_good_422⟩, ⟨row_423, good_423, entry_good_423⟩, trivial⟩
