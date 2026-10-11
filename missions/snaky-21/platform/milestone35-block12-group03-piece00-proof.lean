import Definitions.Def_Snaky35Cache12
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_20 (j : ℕ) (hj : j < 20) : entryAt (406 + j) = tableChunk_20[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_3 : rowAt 3 = data_3 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.1).1
theorem row_110 : rowAt 110 = data_110 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_133 : rowAt 133 = data_133 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.1).1
theorem row_136 : rowAt 136 = data_136 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.1).1
theorem row_164 : rowAt 164 = data_164 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_177 : rowAt 177 = data_177 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_185 : rowAt 185 = data_185 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_199 : rowAt 199 = data_199 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.1).1
theorem row_205 : rowAt 205 = data_205 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_223 : rowAt 223 = data_223 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_229 : rowAt 229 = data_229 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.1).1
theorem row_246 : rowAt 246 = data_246 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_357 : rowAt 357 = data_357 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.1).1
theorem row_371 : rowAt 371 = data_371 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_374 : rowAt 374 = data_374 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_379 : rowAt 379 = data_379 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_384 : rowAt 384 = data_384 := (OAI.SnakyCertificate.MilestoneChecks.block12_group00_correct.1).1
theorem row_403 : rowAt 403 = data_403 := (OAI.SnakyCertificate.MilestoneChecks.block12_group02_correct.2.2.2.1).1
theorem row_405 : rowAt 405 = data_405 := (OAI.SnakyCertificate.MilestoneChecks.block12_group02_correct.2.2.2.2.2.1).1
theorem entry_408_checked : entryAt 408 = entry_408 := by
  rw [entry_chunk_20 2 (by decide)]
  decide +kernel
theorem row_408 : rowAt 408 = data_408 := by
  rw [rowAt, dif_neg (by decide : ¬ 408 < 6), entry_408_checked]
  change forkRow [placeRow ⟨357, 0, 5, 2⟩ (rowAt 357), placeRow ⟨229, 7, 2, 4⟩ (rowAt 229), placeRow ⟨223, 4, 2, 4⟩ (rowAt 223), placeRow ⟨223, 0, 6, 4⟩ (rowAt 223)] = data_408
  rw [row_357, row_229, row_223]
  apply row_ext <;> decide +kernel
theorem entry_good_408 : EntryGood 408 := by
  unfold EntryGood
  rw [entry_408_checked]
  decide +kernel
theorem good_408 : Good (rowAt 408) := by
  rw [row_408]
  unfold Good
  decide +kernel

theorem entry_409_checked : entryAt 409 = entry_409 := by
  rw [entry_chunk_20 3 (by decide)]
  decide +kernel
theorem row_409 : rowAt 409 = data_409 := by
  rw [rowAt, dif_neg (by decide : ¬ 409 < 6), entry_409_checked]
  change forkRow [placeRow ⟨136, 6, 4, 3⟩ (rowAt 136), placeRow ⟨384, 0, 5, 4⟩ (rowAt 384), placeRow ⟨133, 4, 4, 3⟩ (rowAt 133), placeRow ⟨110, 3, 4, 3⟩ (rowAt 110)] = data_409
  rw [row_136, row_384, row_133, row_110]
  apply row_ext <;> decide +kernel
theorem entry_good_409 : EntryGood 409 := by
  unfold EntryGood
  rw [entry_409_checked]
  decide +kernel
theorem good_409 : Good (rowAt 409) := by
  rw [row_409]
  unfold Good
  decide +kernel

theorem entry_410_checked : entryAt 410 = entry_410 := by
  rw [entry_chunk_20 4 (by decide)]
  decide +kernel
theorem row_410 : rowAt 410 = data_410 := by
  rw [rowAt, dif_neg (by decide : ¬ 410 < 6), entry_410_checked]
  change forkRow [placeRow ⟨0, 4, 5, 4⟩ (rowAt 0), placeRow ⟨405, 0, 3, 7⟩ (rowAt 405)] = data_410
  rw [row_0, row_405]
  apply row_ext <;> decide +kernel
theorem entry_good_410 : EntryGood 410 := by
  unfold EntryGood
  rw [entry_410_checked]
  decide +kernel
theorem good_410 : Good (rowAt 410) := by
  rw [row_410]
  unfold Good
  decide +kernel

theorem entry_411_checked : entryAt 411 = entry_411 := by
  rw [entry_chunk_20 5 (by decide)]
  decide +kernel
theorem row_411 : rowAt 411 = data_411 := by
  rw [rowAt, dif_neg (by decide : ¬ 411 < 6), entry_411_checked]
  change forkRow [placeRow ⟨252, 0, 7, 4⟩ (rowAt 252), placeRow ⟨263, 0, 7, 4⟩ (rowAt 263), placeRow ⟨300, 3, 3, 4⟩ (rowAt 300), placeRow ⟨379, 1, 7, 4⟩ (rowAt 379), placeRow ⟨173, 0, 7, 4⟩ (rowAt 173), placeRow ⟨246, 0, 7, 4⟩ (rowAt 246)] = data_411
  rw [row_252, row_263, row_300, row_379, row_173, row_246]
  apply row_ext <;> decide +kernel
theorem entry_good_411 : EntryGood 411 := by
  unfold EntryGood
  rw [entry_411_checked]
  decide +kernel
theorem good_411 : Good (rowAt 411) := by
  rw [row_411]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 408 = data_408 ∧ Good (rowAt 408) ∧ EntryGood 408) ∧ (rowAt 409 = data_409 ∧ Good (rowAt 409) ∧ EntryGood 409) ∧ (rowAt 410 = data_410 ∧ Good (rowAt 410) ∧ EntryGood 410) ∧ (rowAt 411 = data_411 ∧ Good (rowAt 411) ∧ EntryGood 411) ∧ True := by
  exact ⟨⟨row_408, good_408, entry_good_408⟩, ⟨row_409, good_409, entry_good_409⟩, ⟨row_410, good_410, entry_good_410⟩, ⟨row_411, good_411, entry_good_411⟩, trivial⟩
