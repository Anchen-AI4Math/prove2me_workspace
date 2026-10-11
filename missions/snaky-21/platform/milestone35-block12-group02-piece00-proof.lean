import Definitions.Def_Snaky35Cache12
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_19 (j : ℕ) (hj : j < 20) : entryAt (386 + j) = tableChunk_19[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_20 (j : ℕ) (hj : j < 20) : entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_29 : rowAt 29 = data_29 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_42 : rowAt 42 = data_42 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_82 : rowAt 82 = data_82 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_202 : rowAt 202 = data_202 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_245 : rowAt 245 = data_245 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_283 : rowAt 283 = data_283 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_285 : rowAt 285 = data_285 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_286 : rowAt 286 = data_286 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_301 : rowAt 301 = data_301 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_364 : rowAt 364 = data_364 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_384 : rowAt 384 = data_384 := (OAI.SnakyCertificate.MilestoneChecks.block12_group00_correct.1).1
theorem row_388 : rowAt 388 = data_388 := (OAI.SnakyCertificate.MilestoneChecks.block12_group00_correct.2.2.2.2.1).1
theorem row_391 : rowAt 391 = data_391 := (OAI.SnakyCertificate.MilestoneChecks.block12_group00_correct.2.2.2.2.2.2.2.1).1
theorem entry_400_checked : entryAt 400 = entry_400 := by
  rw [entry_chunk_19 14 (by decide)]
  decide +kernel
theorem row_400 : rowAt 400 = data_400 := by
  rw [rowAt, dif_neg (by decide : ¬ 400 < 6), entry_400_checked]
  change forkRow [placeRow ⟨283, 4, 2, 4⟩ (rowAt 283), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252), placeRow ⟨176, 4, 2, 4⟩ (rowAt 176), placeRow ⟨197, 0, 6, 4⟩ (rowAt 197), placeRow ⟨283, 0, 6, 4⟩ (rowAt 283), placeRow ⟨245, 4, 2, 4⟩ (rowAt 245)] = data_400
  rw [row_283, row_252, row_176, row_197, row_245]
  apply row_ext <;> decide +kernel
theorem entry_good_400 : EntryGood 400 := by
  unfold EntryGood
  rw [entry_400_checked]
  decide +kernel
theorem good_400 : Good (rowAt 400) := by
  rw [row_400]
  unfold Good
  decide +kernel

theorem entry_401_checked : entryAt 401 = entry_401 := by
  rw [entry_chunk_19 15 (by decide)]
  decide +kernel
theorem row_401 : rowAt 401 = data_401 := by
  rw [rowAt, dif_neg (by decide : ¬ 401 < 6), entry_401_checked]
  change forkRow [placeRow ⟨24, 7, 3, 2⟩ (rowAt 24), placeRow ⟨286, 0, 4, 6⟩ (rowAt 286), placeRow ⟨364, 2, 4, 2⟩ (rowAt 364), placeRow ⟨319, 1, 3, 6⟩ (rowAt 319)] = data_401
  rw [row_24, row_286, row_364, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_401 : EntryGood 401 := by
  unfold EntryGood
  rw [entry_401_checked]
  decide +kernel
theorem good_401 : Good (rowAt 401) := by
  rw [row_401]
  unfold Good
  decide +kernel

theorem entry_402_checked : entryAt 402 = entry_402 := by
  rw [entry_chunk_19 16 (by decide)]
  decide +kernel
theorem row_402 : rowAt 402 = data_402 := by
  rw [rowAt, dif_neg (by decide : ¬ 402 < 6), entry_402_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨384, 0, 5, 4⟩ (rowAt 384)] = data_402
  rw [row_29, row_384]
  apply row_ext <;> decide +kernel
theorem entry_good_402 : EntryGood 402 := by
  unfold EntryGood
  rw [entry_402_checked]
  decide +kernel
theorem good_402 : Good (rowAt 402) := by
  rw [row_402]
  unfold Good
  decide +kernel

theorem entry_403_checked : entryAt 403 = entry_403 := by
  rw [entry_chunk_19 17 (by decide)]
  decide +kernel
theorem row_403 : rowAt 403 = data_403 := by
  rw [rowAt, dif_neg (by decide : ¬ 403 < 6), entry_403_checked]
  change forkRow [placeRow ⟨202, 1, 4, 5⟩ (rowAt 202), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨314, 4, 5, 4⟩ (rowAt 314), placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨388, 0, 3, 4⟩ (rowAt 388)] = data_403
  rw [row_202, row_180, row_314, row_63, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_403 : EntryGood 403 := by
  unfold EntryGood
  rw [entry_403_checked]
  decide +kernel
theorem good_403 : Good (rowAt 403) := by
  rw [row_403]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 400 = data_400 ∧ Good (rowAt 400) ∧ EntryGood 400) ∧ (rowAt 401 = data_401 ∧ Good (rowAt 401) ∧ EntryGood 401) ∧ (rowAt 402 = data_402 ∧ Good (rowAt 402) ∧ EntryGood 402) ∧ (rowAt 403 = data_403 ∧ Good (rowAt 403) ∧ EntryGood 403) ∧ True := by
  exact ⟨⟨row_400, good_400, entry_good_400⟩, ⟨row_401, good_401, entry_good_401⟩, ⟨row_402, good_402, entry_good_402⟩, ⟨row_403, good_403, entry_good_403⟩, trivial⟩
