import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_17 (j : ℕ) (hj : j < 20) : entryAt (346 + j) = tableChunk_17[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_17 : rowAt 17 = data_17 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_24 : rowAt 24 = data_24 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_60 : rowAt 60 = data_60 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_114 : rowAt 114 = data_114 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_139 : rowAt 139 = data_139 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_255 : rowAt 255 = data_255 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_262 : rowAt 262 = data_262 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_276 : rowAt 276 = data_276 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_287 : rowAt 287 = data_287 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_312 : rowAt 312 = data_312 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_320 : rowAt 320 = data_320 := (OAI.SnakyCertificate.MilestoneChecks.block10_group00_correct.1).1
theorem row_332 : rowAt 332 = data_332 := (OAI.SnakyCertificate.MilestoneChecks.block10_group01_correct.2.2.2.2.1).1
theorem row_339 : rowAt 339 = data_339 := (OAI.SnakyCertificate.MilestoneChecks.block10_group02_correct.2.2.2.1).1
theorem entry_348_checked : entryAt 348 = entry_348 := by
  rw [entry_chunk_17 2 (by decide)]
  decide +kernel
theorem row_348 : rowAt 348 = data_348 := by
  rw [rowAt, dif_neg (by decide : ¬ 348 < 6), entry_348_checked]
  change forkRow [placeRow ⟨312, 1, 5, 5⟩ (rowAt 312), placeRow ⟨114, 4, 3, 4⟩ (rowAt 114), placeRow ⟨139, 3, 4, 5⟩ (rowAt 139)] = data_348
  rw [row_312, row_114, row_139]
  apply row_ext <;> decide +kernel
theorem entry_good_348 : EntryGood 348 := by
  unfold EntryGood
  rw [entry_348_checked]
  decide +kernel
theorem good_348 : Good (rowAt 348) := by
  rw [row_348]
  unfold Good
  decide +kernel

theorem entry_349_checked : entryAt 349 = entry_349 := by
  rw [entry_chunk_17 3 (by decide)]
  decide +kernel
theorem row_349 : rowAt 349 = data_349 := by
  rw [rowAt, dif_neg (by decide : ¬ 349 < 6), entry_349_checked]
  change forkRow [placeRow ⟨14, 1, 4, 5⟩ (rowAt 14), placeRow ⟨17, 1, 4, 5⟩ (rowAt 17), placeRow ⟨332, 0, 3, 4⟩ (rowAt 332)] = data_349
  rw [row_14, row_17, row_332]
  apply row_ext <;> decide +kernel
theorem entry_good_349 : EntryGood 349 := by
  unfold EntryGood
  rw [entry_349_checked]
  decide +kernel
theorem good_349 : Good (rowAt 349) := by
  rw [row_349]
  unfold Good
  decide +kernel

theorem entry_350_checked : entryAt 350 = entry_350 := by
  rw [entry_chunk_17 4 (by decide)]
  decide +kernel
theorem row_350 : rowAt 350 = data_350 := by
  rw [rowAt, dif_neg (by decide : ¬ 350 < 6), entry_350_checked]
  change forkRow [placeRow ⟨24, 4, 2, 5⟩ (rowAt 24), placeRow ⟨107, 2, 6, 4⟩ (rowAt 107), placeRow ⟨271, 4, 5, 5⟩ (rowAt 271), placeRow ⟨215, 0, 5, 5⟩ (rowAt 215)] = data_350
  rw [row_24, row_107, row_271, row_215]
  apply row_ext <;> decide +kernel
theorem entry_good_350 : EntryGood 350 := by
  unfold EntryGood
  rw [entry_350_checked]
  decide +kernel
theorem good_350 : Good (rowAt 350) := by
  rw [row_350]
  unfold Good
  decide +kernel

theorem entry_351_checked : entryAt 351 = entry_351 := by
  rw [entry_chunk_17 5 (by decide)]
  decide +kernel
theorem row_351 : rowAt 351 = data_351 := by
  rw [rowAt, dif_neg (by decide : ¬ 351 < 6), entry_351_checked]
  change forkRow [placeRow ⟨163, 0, 5, 4⟩ (rowAt 163), placeRow ⟨287, 4, 1, 4⟩ (rowAt 287), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25)] = data_351
  rw [row_163, row_287, row_25]
  apply row_ext <;> decide +kernel
theorem entry_good_351 : EntryGood 351 := by
  unfold EntryGood
  rw [entry_351_checked]
  decide +kernel
theorem good_351 : Good (rowAt 351) := by
  rw [row_351]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 348 = data_348 ∧ Good (rowAt 348) ∧ EntryGood 348) ∧ (rowAt 349 = data_349 ∧ Good (rowAt 349) ∧ EntryGood 349) ∧ (rowAt 350 = data_350 ∧ Good (rowAt 350) ∧ EntryGood 350) ∧ (rowAt 351 = data_351 ∧ Good (rowAt 351) ∧ EntryGood 351) ∧ True := by
  exact ⟨⟨row_348, good_348, entry_good_348⟩, ⟨row_349, good_349, entry_good_349⟩, ⟨row_350, good_350, entry_good_350⟩, ⟨row_351, good_351, entry_good_351⟩, trivial⟩
