import Definitions.Def_Snaky35Cache11
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_18 (j : ℕ) (hj : j < 20) : entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_29 : rowAt 29 = data_29 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_101 : rowAt 101 = data_101 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.1).1
theorem row_124 : rowAt 124 = data_124 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_183 : rowAt 183 = data_183 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_211 : rowAt 211 = data_211 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_285 : rowAt 285 = data_285 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_294 : rowAt 294 = data_294 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_341 : rowAt 341 = data_341 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_362 : rowAt 362 = data_362 := (OAI.SnakyCertificate.MilestoneChecks.block11_group01_correct.2.2.1).1
theorem row_368 : rowAt 368 = data_368 := (OAI.SnakyCertificate.MilestoneChecks.block11_group02_correct.1).1
theorem entry_376_checked : entryAt 376 = entry_376 := by
  rw [entry_chunk_18 10 (by decide)]
  decide +kernel
theorem row_376 : rowAt 376 = data_376 := by
  rw [rowAt, dif_neg (by decide : ¬ 376 < 6), entry_376_checked]
  change forkRow [placeRow ⟨162, 1, 5, 4⟩ (rowAt 162), placeRow ⟨285, 3, 1, 3⟩ (rowAt 285)] = data_376
  rw [row_162, row_285]
  apply row_ext <;> decide +kernel
theorem entry_good_376 : EntryGood 376 := by
  unfold EntryGood
  rw [entry_376_checked]
  decide +kernel
theorem good_376 : Good (rowAt 376) := by
  rw [row_376]
  unfold Good
  decide +kernel

theorem entry_377_checked : entryAt 377 = entry_377 := by
  rw [entry_chunk_18 11 (by decide)]
  decide +kernel
theorem row_377 : rowAt 377 = data_377 := by
  rw [rowAt, dif_neg (by decide : ¬ 377 < 6), entry_377_checked]
  change forkRow [placeRow ⟨29, 3, 3, 0⟩ (rowAt 29), placeRow ⟨362, 0, 7, 2⟩ (rowAt 362)] = data_377
  rw [row_29, row_362]
  apply row_ext <;> decide +kernel
theorem entry_good_377 : EntryGood 377 := by
  unfold EntryGood
  rw [entry_377_checked]
  decide +kernel
theorem good_377 : Good (rowAt 377) := by
  rw [row_377]
  unfold Good
  decide +kernel

theorem entry_378_checked : entryAt 378 = entry_378 := by
  rw [entry_chunk_18 12 (by decide)]
  decide +kernel
theorem row_378 : rowAt 378 = data_378 := by
  rw [rowAt, dif_neg (by decide : ¬ 378 < 6), entry_378_checked]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨176, 4, 1, 4⟩ (rowAt 176), placeRow ⟨183, 4, 1, 4⟩ (rowAt 183), placeRow ⟨172, 6, 1, 4⟩ (rowAt 172), placeRow ⟨294, 4, 1, 4⟩ (rowAt 294)] = data_378
  rw [row_295, row_176, row_183, row_172, row_294]
  apply row_ext <;> decide +kernel
theorem entry_good_378 : EntryGood 378 := by
  unfold EntryGood
  rw [entry_378_checked]
  decide +kernel
theorem good_378 : Good (rowAt 378) := by
  rw [row_378]
  unfold Good
  decide +kernel

theorem entry_379_checked : entryAt 379 = entry_379 := by
  rw [entry_chunk_18 13 (by decide)]
  decide +kernel
theorem row_379 : rowAt 379 = data_379 := by
  rw [rowAt, dif_neg (by decide : ¬ 379 < 6), entry_379_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55), placeRow ⟨368, 0, 5, 4⟩ (rowAt 368)] = data_379
  rw [row_63, row_64, row_55, row_368]
  apply row_ext <;> decide +kernel
theorem entry_good_379 : EntryGood 379 := by
  unfold EntryGood
  rw [entry_379_checked]
  decide +kernel
theorem good_379 : Good (rowAt 379) := by
  rw [row_379]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 376 = data_376 ∧ Good (rowAt 376) ∧ EntryGood 376) ∧ (rowAt 377 = data_377 ∧ Good (rowAt 377) ∧ EntryGood 377) ∧ (rowAt 378 = data_378 ∧ Good (rowAt 378) ∧ EntryGood 378) ∧ (rowAt 379 = data_379 ∧ Good (rowAt 379) ∧ EntryGood 379) ∧ True := by
  exact ⟨⟨row_376, good_376, entry_good_376⟩, ⟨row_377, good_377, entry_good_377⟩, ⟨row_378, good_378, entry_good_378⟩, ⟨row_379, good_379, entry_good_379⟩, trivial⟩
