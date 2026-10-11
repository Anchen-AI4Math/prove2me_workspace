import Definitions.Def_Snaky35Cache10
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_16 (j : ℕ) (hj : j < 20) : entryAt (326 + j) = tableChunk_16[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_1 : rowAt 1 = data_1 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.1).1
theorem row_15 : rowAt 15 = data_15 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_44 : rowAt 44 = data_44 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_49 : rowAt 49 = data_49 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_67 : rowAt 67 = data_67 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.1).1
theorem row_90 : rowAt 90 = data_90 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_113 : rowAt 113 = data_113 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_154 : rowAt 154 = data_154 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_155 : rowAt 155 = data_155 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_162 : rowAt 162 = data_162 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.1).1
theorem row_196 : rowAt 196 = data_196 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.1).1
theorem row_268 : rowAt 268 = data_268 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_285 : rowAt 285 = data_285 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_289 : rowAt 289 = data_289 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.1).1
theorem row_298 : rowAt 298 = data_298 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_305 : rowAt 305 = data_305 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_317 : rowAt 317 = data_317 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_328_checked : entryAt 328 = entry_328 := by
  rw [entry_chunk_16 2 (by decide)]
  decide +kernel
theorem row_328 : rowAt 328 = data_328 := by
  rw [rowAt, dif_neg (by decide : ¬ 328 < 6), entry_328_checked]
  change forkRow [placeRow ⟨49, 0, 4, 5⟩ (rowAt 49), placeRow ⟨44, 3, 4, 5⟩ (rowAt 44), placeRow ⟨285, 0, 3, 4⟩ (rowAt 285)] = data_328
  rw [row_49, row_44, row_285]
  apply row_ext <;> decide +kernel
theorem entry_good_328 : EntryGood 328 := by
  unfold EntryGood
  rw [entry_328_checked]
  decide +kernel
theorem good_328 : Good (rowAt 328) := by
  rw [row_328]
  unfold Good
  decide +kernel

theorem entry_329_checked : entryAt 329 = entry_329 := by
  rw [entry_chunk_16 3 (by decide)]
  decide +kernel
theorem row_329 : rowAt 329 = data_329 := by
  rw [rowAt, dif_neg (by decide : ¬ 329 < 6), entry_329_checked]
  change forkRow [placeRow ⟨0, 7, 4, 6⟩ (rowAt 0), placeRow ⟨305, 0, 5, 5⟩ (rowAt 305)] = data_329
  rw [row_0, row_305]
  apply row_ext <;> decide +kernel
theorem entry_good_329 : EntryGood 329 := by
  unfold EntryGood
  rw [entry_329_checked]
  decide +kernel
theorem good_329 : Good (rowAt 329) := by
  rw [row_329]
  unfold Good
  decide +kernel

theorem entry_330_checked : entryAt 330 = entry_330 := by
  rw [entry_chunk_16 4 (by decide)]
  decide +kernel
theorem row_330 : rowAt 330 = data_330 := by
  rw [rowAt, dif_neg (by decide : ¬ 330 < 6), entry_330_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨268, 0, 4, 5⟩ (rowAt 268), placeRow ⟨144, 0, 5, 4⟩ (rowAt 144), placeRow ⟨154, 4, 5, 4⟩ (rowAt 154), placeRow ⟨155, 5, 5, 4⟩ (rowAt 155)] = data_330
  rw [row_63, row_268, row_144, row_154, row_155]
  apply row_ext <;> decide +kernel
theorem entry_good_330 : EntryGood 330 := by
  unfold EntryGood
  rw [entry_330_checked]
  decide +kernel
theorem good_330 : Good (rowAt 330) := by
  rw [row_330]
  unfold Good
  decide +kernel

theorem entry_331_checked : entryAt 331 = entry_331 := by
  rw [entry_chunk_16 5 (by decide)]
  decide +kernel
theorem row_331 : rowAt 331 = data_331 := by
  rw [rowAt, dif_neg (by decide : ¬ 331 < 6), entry_331_checked]
  change forkRow [placeRow ⟨113, 0, 1, 4⟩ (rowAt 113), placeRow ⟨15, 0, 3, 4⟩ (rowAt 15), placeRow ⟨298, 4, 4, 5⟩ (rowAt 298), placeRow ⟨90, 2, 5, 4⟩ (rowAt 90)] = data_331
  rw [row_113, row_15, row_298, row_90]
  apply row_ext <;> decide +kernel
theorem entry_good_331 : EntryGood 331 := by
  unfold EntryGood
  rw [entry_331_checked]
  decide +kernel
theorem good_331 : Good (rowAt 331) := by
  rw [row_331]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 328 = data_328 ∧ Good (rowAt 328) ∧ EntryGood 328) ∧ (rowAt 329 = data_329 ∧ Good (rowAt 329) ∧ EntryGood 329) ∧ (rowAt 330 = data_330 ∧ Good (rowAt 330) ∧ EntryGood 330) ∧ (rowAt 331 = data_331 ∧ Good (rowAt 331) ∧ EntryGood 331) ∧ True := by
  exact ⟨⟨row_328, good_328, entry_good_328⟩, ⟨row_329, good_329, entry_good_329⟩, ⟨row_330, good_330, entry_good_330⟩, ⟨row_331, good_331, entry_good_331⟩, trivial⟩
