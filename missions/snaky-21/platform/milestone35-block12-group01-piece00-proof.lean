import Definitions.Def_Snaky35Cache12
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_19 (j : ℕ) (hj : j < 20) : entryAt (386 + j) = tableChunk_19[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_65 : rowAt 65 = data_65 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_130 : rowAt 130 = data_130 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_211 : rowAt 211 = data_211 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_226 : rowAt 226 = data_226 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_257 : rowAt 257 = data_257 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_303 : rowAt 303 = data_303 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_327 : rowAt 327 = data_327 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.1).1
theorem row_348 : rowAt 348 = data_348 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_363 : rowAt 363 = data_363 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_364 : rowAt 364 = data_364 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_365 : rowAt 365 = data_365 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_374 : rowAt 374 = data_374 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_376 : rowAt 376 = data_376 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_392_checked : entryAt 392 = entry_392 := by
  rw [entry_chunk_19 6 (by decide)]
  decide +kernel
theorem row_392 : rowAt 392 = data_392 := by
  rw [rowAt, dif_neg (by decide : ¬ 392 < 6), entry_392_checked]
  change forkRow [placeRow ⟨24, 7, 3, 1⟩ (rowAt 24), placeRow ⟨107, 1, 4, 5⟩ (rowAt 107), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨364, 2, 4, 1⟩ (rowAt 364)] = data_392
  rw [row_24, row_107, row_236, row_364]
  apply row_ext <;> decide +kernel
theorem entry_good_392 : EntryGood 392 := by
  unfold EntryGood
  rw [entry_392_checked]
  decide +kernel
theorem good_392 : Good (rowAt 392) := by
  rw [row_392]
  unfold Good
  decide +kernel

theorem entry_393_checked : entryAt 393 = entry_393 := by
  rw [entry_chunk_19 7 (by decide)]
  decide +kernel
theorem row_393 : rowAt 393 = data_393 := by
  rw [rowAt, dif_neg (by decide : ¬ 393 < 6), entry_393_checked]
  change forkRow [placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨348, 0, 6, 3⟩ (rowAt 348), placeRow ⟨65, 3, 4, 5⟩ (rowAt 65), placeRow ⟨303, 0, 4, 5⟩ (rowAt 303)] = data_393
  rw [row_107, row_348, row_65, row_303]
  apply row_ext <;> decide +kernel
theorem entry_good_393 : EntryGood 393 := by
  unfold EntryGood
  rw [entry_393_checked]
  decide +kernel
theorem good_393 : Good (rowAt 393) := by
  rw [row_393]
  unfold Good
  decide +kernel

theorem entry_394_checked : entryAt 394 = entry_394 := by
  rw [entry_chunk_19 8 (by decide)]
  decide +kernel
theorem row_394 : rowAt 394 = data_394 := by
  rw [rowAt, dif_neg (by decide : ¬ 394 < 6), entry_394_checked]
  change forkRow [placeRow ⟨226, 4, 1, 4⟩ (rowAt 226), placeRow ⟨226, 0, 5, 4⟩ (rowAt 226), placeRow ⟨327, 4, 3, 4⟩ (rowAt 327), placeRow ⟨327, 6, 3, 3⟩ (rowAt 327), placeRow ⟨226, 6, 1, 3⟩ (rowAt 226), placeRow ⟨226, 2, 5, 3⟩ (rowAt 226)] = data_394
  rw [row_226, row_327]
  apply row_ext <;> decide +kernel
theorem entry_good_394 : EntryGood 394 := by
  unfold EntryGood
  rw [entry_394_checked]
  decide +kernel
theorem good_394 : Good (rowAt 394) := by
  rw [row_394]
  unfold Good
  decide +kernel

theorem entry_395_checked : entryAt 395 = entry_395 := by
  rw [entry_chunk_19 9 (by decide)]
  decide +kernel
theorem row_395 : rowAt 395 = data_395 := by
  rw [rowAt, dif_neg (by decide : ¬ 395 < 6), entry_395_checked]
  change forkRow [placeRow ⟨211, 4, 2, 4⟩ (rowAt 211), placeRow ⟨376, 0, 6, 4⟩ (rowAt 376), placeRow ⟨24, 2, 6, 3⟩ (rowAt 24), placeRow ⟨236, 3, 2, 5⟩ (rowAt 236)] = data_395
  rw [row_211, row_376, row_24, row_236]
  apply row_ext <;> decide +kernel
theorem entry_good_395 : EntryGood 395 := by
  unfold EntryGood
  rw [entry_395_checked]
  decide +kernel
theorem good_395 : Good (rowAt 395) := by
  rw [row_395]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 392 = data_392 ∧ Good (rowAt 392) ∧ EntryGood 392) ∧ (rowAt 393 = data_393 ∧ Good (rowAt 393) ∧ EntryGood 393) ∧ (rowAt 394 = data_394 ∧ Good (rowAt 394) ∧ EntryGood 394) ∧ (rowAt 395 = data_395 ∧ Good (rowAt 395) ∧ EntryGood 395) ∧ True := by
  exact ⟨⟨row_392, good_392, entry_good_392⟩, ⟨row_393, good_393, entry_good_393⟩, ⟨row_394, good_394, entry_good_394⟩, ⟨row_395, good_395, entry_good_395⟩, trivial⟩
