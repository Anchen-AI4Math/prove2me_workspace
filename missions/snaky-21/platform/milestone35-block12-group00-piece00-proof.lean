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
theorem entry_384_checked : entryAt 384 = entry_384 := by
  rw [entry_chunk_18 18 (by decide)]
  decide +kernel
theorem row_384 : rowAt 384 = data_384 := by
  rw [rowAt, dif_neg (by decide : ¬ 384 < 6), entry_384_checked]
  change forkRow [placeRow ⟨173, 2, 6, 4⟩ (rowAt 173), placeRow ⟨282, 4, 2, 4⟩ (rowAt 282), placeRow ⟨220, 2, 6, 4⟩ (rowAt 220), placeRow ⟨246, 2, 6, 4⟩ (rowAt 246), placeRow ⟨263, 2, 6, 4⟩ (rowAt 263), placeRow ⟨183, 6, 2, 4⟩ (rowAt 183), placeRow ⟨295, 0, 6, 4⟩ (rowAt 295)] = data_384
  rw [row_173, row_282, row_220, row_246, row_263, row_183, row_295]
  apply row_ext <;> decide +kernel
theorem entry_good_384 : EntryGood 384 := by
  unfold EntryGood
  rw [entry_384_checked]
  decide +kernel
theorem good_384 : Good (rowAt 384) := by
  rw [row_384]
  unfold Good
  decide +kernel

theorem entry_385_checked : entryAt 385 = entry_385 := by
  rw [entry_chunk_18 19 (by decide)]
  decide +kernel
theorem row_385 : rowAt 385 = data_385 := by
  rw [rowAt, dif_neg (by decide : ¬ 385 < 6), entry_385_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨369, 4, 1, 5⟩ (rowAt 369)] = data_385
  rw [row_63, row_64, row_55, row_369]
  apply row_ext <;> decide +kernel
theorem entry_good_385 : EntryGood 385 := by
  unfold EntryGood
  rw [entry_385_checked]
  decide +kernel
theorem good_385 : Good (rowAt 385) := by
  rw [row_385]
  unfold Good
  decide +kernel

theorem entry_386_checked : entryAt 386 = entry_386 := by
  rw [entry_chunk_19 0 (by decide)]
  decide +kernel
theorem row_386 : rowAt 386 = data_386 := by
  rw [rowAt, dif_neg (by decide : ¬ 386 < 6), entry_386_checked]
  change forkRow [placeRow ⟨217, 4, 1, 4⟩ (rowAt 217), placeRow ⟨172, 0, 5, 4⟩ (rowAt 172), placeRow ⟨173, 4, 1, 4⟩ (rowAt 173), placeRow ⟨217, 0, 5, 4⟩ (rowAt 217), placeRow ⟨294, 0, 5, 4⟩ (rowAt 294), placeRow ⟨294, 4, 1, 4⟩ (rowAt 294)] = data_386
  rw [row_217, row_172, row_173, row_294]
  apply row_ext <;> decide +kernel
theorem entry_good_386 : EntryGood 386 := by
  unfold EntryGood
  rw [entry_386_checked]
  decide +kernel
theorem good_386 : Good (rowAt 386) := by
  rw [row_386]
  unfold Good
  decide +kernel

theorem entry_387_checked : entryAt 387 = entry_387 := by
  rw [entry_chunk_19 1 (by decide)]
  decide +kernel
theorem row_387 : rowAt 387 = data_387 := by
  rw [rowAt, dif_neg (by decide : ¬ 387 < 6), entry_387_checked]
  change forkRow [placeRow ⟨14, 1, 4, 6⟩ (rowAt 14), placeRow ⟨370, 0, 5, 4⟩ (rowAt 370)] = data_387
  rw [row_14, row_370]
  apply row_ext <;> decide +kernel
theorem entry_good_387 : EntryGood 387 := by
  unfold EntryGood
  rw [entry_387_checked]
  decide +kernel
theorem good_387 : Good (rowAt 387) := by
  rw [row_387]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 384 = data_384 ∧ Good (rowAt 384) ∧ EntryGood 384) ∧ (rowAt 385 = data_385 ∧ Good (rowAt 385) ∧ EntryGood 385) ∧ (rowAt 386 = data_386 ∧ Good (rowAt 386) ∧ EntryGood 386) ∧ (rowAt 387 = data_387 ∧ Good (rowAt 387) ∧ EntryGood 387) ∧ True := by
  exact ⟨⟨row_384, good_384, entry_good_384⟩, ⟨row_385, good_385, entry_good_385⟩, ⟨row_386, good_386, entry_good_386⟩, ⟨row_387, good_387, entry_good_387⟩, trivial⟩
