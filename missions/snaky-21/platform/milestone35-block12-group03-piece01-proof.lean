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
theorem entry_412_checked : entryAt 412 = entry_412 := by
  rw [entry_chunk_20 6 (by decide)]
  decide +kernel
theorem row_412 : rowAt 412 = data_412 := by
  rw [rowAt, dif_neg (by decide : ¬ 412 < 6), entry_412_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨403, 4, 3, 6⟩ (rowAt 403)] = data_412
  rw [row_0, row_403]
  apply row_ext <;> decide +kernel
theorem entry_good_412 : EntryGood 412 := by
  unfold EntryGood
  rw [entry_412_checked]
  decide +kernel
theorem good_412 : Good (rowAt 412) := by
  rw [row_412]
  unfold Good
  decide +kernel

theorem entry_413_checked : entryAt 413 = entry_413 := by
  rw [entry_chunk_20 7 (by decide)]
  decide +kernel
theorem row_413 : rowAt 413 = data_413 := by
  rw [rowAt, dif_neg (by decide : ¬ 413 < 6), entry_413_checked]
  change forkRow [placeRow ⟨3, 7, 4, 3⟩ (rowAt 3), placeRow ⟨403, 0, 4, 7⟩ (rowAt 403)] = data_413
  rw [row_3, row_403]
  apply row_ext <;> decide +kernel
theorem entry_good_413 : EntryGood 413 := by
  unfold EntryGood
  rw [entry_413_checked]
  decide +kernel
theorem good_413 : Good (rowAt 413) := by
  rw [row_413]
  unfold Good
  decide +kernel

theorem entry_414_checked : entryAt 414 = entry_414 := by
  rw [entry_chunk_20 8 (by decide)]
  decide +kernel
theorem row_414 : rowAt 414 = data_414 := by
  rw [rowAt, dif_neg (by decide : ¬ 414 < 6), entry_414_checked]
  change forkRow [placeRow ⟨374, 0, 2, 5⟩ (rowAt 374), placeRow ⟨199, 2, 4, 2⟩ (rowAt 199), placeRow ⟨185, 2, 4, 2⟩ (rowAt 185)] = data_414
  rw [row_374, row_199, row_185]
  apply row_ext <;> decide +kernel
theorem entry_good_414 : EntryGood 414 := by
  unfold EntryGood
  rw [entry_414_checked]
  decide +kernel
theorem good_414 : Good (rowAt 414) := by
  rw [row_414]
  unfold Good
  decide +kernel

theorem entry_415_checked : entryAt 415 = entry_415 := by
  rw [entry_chunk_20 9 (by decide)]
  decide +kernel
theorem row_415 : rowAt 415 = data_415 := by
  rw [rowAt, dif_neg (by decide : ¬ 415 < 6), entry_415_checked]
  change forkRow [placeRow ⟨177, 1, 4, 2⟩ (rowAt 177), placeRow ⟨164, 1, 4, 2⟩ (rowAt 164), placeRow ⟨205, 1, 5, 2⟩ (rowAt 205), placeRow ⟨384, 0, 3, 4⟩ (rowAt 384), placeRow ⟨371, 0, 5, 4⟩ (rowAt 371)] = data_415
  rw [row_177, row_164, row_205, row_384, row_371]
  apply row_ext <;> decide +kernel
theorem entry_good_415 : EntryGood 415 := by
  unfold EntryGood
  rw [entry_415_checked]
  decide +kernel
theorem good_415 : Good (rowAt 415) := by
  rw [row_415]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 412 = data_412 ∧ Good (rowAt 412) ∧ EntryGood 412) ∧ (rowAt 413 = data_413 ∧ Good (rowAt 413) ∧ EntryGood 413) ∧ (rowAt 414 = data_414 ∧ Good (rowAt 414) ∧ EntryGood 414) ∧ (rowAt 415 = data_415 ∧ Good (rowAt 415) ∧ EntryGood 415) ∧ True := by
  exact ⟨⟨row_412, good_412, entry_good_412⟩, ⟨row_413, good_413, entry_good_413⟩, ⟨row_414, good_414, entry_good_414⟩, ⟨row_415, good_415, entry_good_415⟩, trivial⟩
