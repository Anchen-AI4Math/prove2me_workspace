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
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_18 (j : ℕ) (hj : j < 20) : entryAt (366 + j) = tableChunk_18[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_19 (j : ℕ) (hj : j < 20) : entryAt (386 + j) = tableChunk_19[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_12 : rowAt 12 = data_12 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_14 : rowAt 14 = data_14 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_172 : rowAt 172 = data_172 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_183 : rowAt 183 = data_183 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_197 : rowAt 197 = data_197 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.1).1
theorem row_215 : rowAt 215 = data_215 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_217 : rowAt 217 = data_217 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_220 : rowAt 220 = data_220 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_246 : rowAt 246 = data_246 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_271 : rowAt 271 = data_271 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_282 : rowAt 282 = data_282 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_294 : rowAt 294 = data_294 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_369 : rowAt 369 = data_369 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_370 : rowAt 370 = data_370 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_372 : rowAt 372 = data_372 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_374 : rowAt 374 = data_374 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_388_checked : entryAt 388 = entry_388 := by
  rw [entry_chunk_19 2 (by decide)]
  decide +kernel
theorem row_388 : rowAt 388 = data_388 := by
  rw [rowAt, dif_neg (by decide : ¬ 388 < 6), entry_388_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨374, 0, 3, 4⟩ (rowAt 374)] = data_388
  rw [row_6, row_374]
  apply row_ext <;> decide +kernel
theorem entry_good_388 : EntryGood 388 := by
  unfold EntryGood
  rw [entry_388_checked]
  decide +kernel
theorem good_388 : Good (rowAt 388) := by
  rw [row_388]
  unfold Good
  decide +kernel

theorem entry_389_checked : entryAt 389 = entry_389 := by
  rw [entry_chunk_19 3 (by decide)]
  decide +kernel
theorem row_389 : rowAt 389 = data_389 := by
  rw [rowAt, dif_neg (by decide : ¬ 389 < 6), entry_389_checked]
  change forkRow [placeRow ⟨197, 5, 4, 1⟩ (rowAt 197), placeRow ⟨215, 7, 3, 2⟩ (rowAt 215), placeRow ⟨271, 3, 3, 2⟩ (rowAt 271), placeRow ⟨236, 0, 5, 5⟩ (rowAt 236), placeRow ⟨192, 6, 4, 1⟩ (rowAt 192)] = data_389
  rw [row_197, row_215, row_271, row_236, row_192]
  apply row_ext <;> decide +kernel
theorem entry_good_389 : EntryGood 389 := by
  unfold EntryGood
  rw [entry_389_checked]
  decide +kernel
theorem good_389 : Good (rowAt 389) := by
  rw [row_389]
  unfold Good
  decide +kernel

theorem entry_390_checked : entryAt 390 = entry_390 := by
  rw [entry_chunk_19 4 (by decide)]
  decide +kernel
theorem row_390 : rowAt 390 = data_390 := by
  rw [rowAt, dif_neg (by decide : ¬ 390 < 6), entry_390_checked]
  change forkRow [placeRow ⟨372, 2, 5, 0⟩ (rowAt 372), placeRow ⟨167, 5, 4, 1⟩ (rowAt 167), placeRow ⟨12, 7, 3, 1⟩ (rowAt 12)] = data_390
  rw [row_372, row_167, row_12]
  apply row_ext <;> decide +kernel
theorem entry_good_390 : EntryGood 390 := by
  unfold EntryGood
  rw [entry_390_checked]
  decide +kernel
theorem good_390 : Good (rowAt 390) := by
  rw [row_390]
  unfold Good
  decide +kernel

theorem entry_391_checked : entryAt 391 = entry_391 := by
  rw [entry_chunk_19 5 (by decide)]
  decide +kernel
theorem row_391 : rowAt 391 = data_391 := by
  rw [rowAt, dif_neg (by decide : ¬ 391 < 6), entry_391_checked]
  change forkRow [placeRow ⟨6, 5, 5, 1⟩ (rowAt 6), placeRow ⟨388, 0, 3, 5⟩ (rowAt 388)] = data_391
  rw [row_6, row_388]
  apply row_ext <;> decide +kernel
theorem entry_good_391 : EntryGood 391 := by
  unfold EntryGood
  rw [entry_391_checked]
  decide +kernel
theorem good_391 : Good (rowAt 391) := by
  rw [row_391]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 388 = data_388 ∧ Good (rowAt 388) ∧ EntryGood 388) ∧ (rowAt 389 = data_389 ∧ Good (rowAt 389) ∧ EntryGood 389) ∧ (rowAt 390 = data_390 ∧ Good (rowAt 390) ∧ EntryGood 390) ∧ (rowAt 391 = data_391 ∧ Good (rowAt 391) ∧ EntryGood 391) ∧ True := by
  exact ⟨⟨row_388, good_388, entry_good_388⟩, ⟨row_389, good_389, entry_good_389⟩, ⟨row_390, good_390, entry_good_390⟩, ⟨row_391, good_391, entry_good_391⟩, trivial⟩
