import Definitions.Def_Snaky35Cache15
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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_24 (j : ℕ) (hj : j < 20) : entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_25 (j : ℕ) (hj : j < 20) : entryAt (506 + j) = tableChunk_25[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_15 : rowAt 15 = data_15 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_33 : rowAt 33 = data_33 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.1).1
theorem row_68 : rowAt 68 = data_68 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.1).1
theorem row_99 : rowAt 99 = data_99 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.1).1
theorem row_151 : rowAt 151 = data_151 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_159 : rowAt 159 = data_159 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_183 : rowAt 183 = data_183 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_200 : rowAt 200 = data_200 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.1).1
theorem row_241 : rowAt 241 = data_241 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_252 : rowAt 252 = data_252 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_282 : rowAt 282 = data_282 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_310 : rowAt 310 = data_310 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_318 : rowAt 318 = data_318 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_331 : rowAt 331 = data_331 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_351 : rowAt 351 = data_351 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_380 : rowAt 380 = data_380 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_381 : rowAt 381 = data_381 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_393 : rowAt 393 = data_393 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_455 : rowAt 455 = data_455 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.1).1
theorem row_481 : rowAt 481 = data_481 := (OAI.SnakyCertificate.MilestoneChecks.block15_group00_correct.2.1).1
theorem row_496 : rowAt 496 = data_496 := (OAI.SnakyCertificate.MilestoneChecks.block15_group02_correct.1).1
theorem row_499 : rowAt 499 = data_499 := (OAI.SnakyCertificate.MilestoneChecks.block15_group02_correct.2.2.2.1).1
theorem entry_508_checked : entryAt 508 = entry_508 := by
  rw [entry_chunk_25 2 (by decide)]
  decide +kernel
theorem row_508 : rowAt 508 = data_508 := by
  rw [rowAt, dif_neg (by decide : ¬ 508 < 6), entry_508_checked]
  change forkRow [placeRow ⟨6, 0, 5, 4⟩ (rowAt 6), placeRow ⟨393, 0, 1, 5⟩ (rowAt 393)] = data_508
  rw [row_6, row_393]
  apply row_ext <;> decide +kernel
theorem entry_good_508 : EntryGood 508 := by
  unfold EntryGood
  rw [entry_508_checked]
  decide +kernel
theorem good_508 : Good (rowAt 508) := by
  rw [row_508]
  unfold Good
  decide +kernel

theorem entry_509_checked : entryAt 509 = entry_509 := by
  rw [entry_chunk_25 3 (by decide)]
  decide +kernel
theorem row_509 : rowAt 509 = data_509 := by
  rw [rowAt, dif_neg (by decide : ¬ 509 < 6), entry_509_checked]
  change forkRow [placeRow ⟨252, 0, 6, 4⟩ (rowAt 252), placeRow ⟨241, 4, 2, 4⟩ (rowAt 241), placeRow ⟨455, 0, 6, 3⟩ (rowAt 455), placeRow ⟨68, 2, 6, 4⟩ (rowAt 68)] = data_509
  rw [row_252, row_241, row_455, row_68]
  apply row_ext <;> decide +kernel
theorem entry_good_509 : EntryGood 509 := by
  unfold EntryGood
  rw [entry_509_checked]
  decide +kernel
theorem good_509 : Good (rowAt 509) := by
  rw [row_509]
  unfold Good
  decide +kernel

theorem entry_510_checked : entryAt 510 = entry_510 := by
  rw [entry_chunk_25 4 (by decide)]
  decide +kernel
theorem row_510 : rowAt 510 = data_510 := by
  rw [rowAt, dif_neg (by decide : ¬ 510 < 6), entry_510_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨508, 0, 7, 4⟩ (rowAt 508)] = data_510
  rw [row_6, row_508]
  apply row_ext <;> decide +kernel
theorem entry_good_510 : EntryGood 510 := by
  unfold EntryGood
  rw [entry_510_checked]
  decide +kernel
theorem good_510 : Good (rowAt 510) := by
  rw [row_510]
  unfold Good
  decide +kernel

theorem entry_511_checked : entryAt 511 = entry_511 := by
  rw [entry_chunk_25 5 (by decide)]
  decide +kernel
theorem row_511 : rowAt 511 = data_511 := by
  rw [rowAt, dif_neg (by decide : ¬ 511 < 6), entry_511_checked]
  change forkRow [placeRow ⟨15, 1, 4, 5⟩ (rowAt 15), placeRow ⟨331, 0, 5, 3⟩ (rowAt 331), placeRow ⟨380, 4, 2, 4⟩ (rowAt 380)] = data_511
  rw [row_15, row_331, row_380]
  apply row_ext <;> decide +kernel
theorem entry_good_511 : EntryGood 511 := by
  unfold EntryGood
  rw [entry_511_checked]
  decide +kernel
theorem good_511 : Good (rowAt 511) := by
  rw [row_511]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 508 = data_508 ∧ Good (rowAt 508) ∧ EntryGood 508) ∧ (rowAt 509 = data_509 ∧ Good (rowAt 509) ∧ EntryGood 509) ∧ (rowAt 510 = data_510 ∧ Good (rowAt 510) ∧ EntryGood 510) ∧ (rowAt 511 = data_511 ∧ Good (rowAt 511) ∧ EntryGood 511) ∧ True := by
  exact ⟨⟨row_508, good_508, entry_good_508⟩, ⟨row_509, good_509, entry_good_509⟩, ⟨row_510, good_510, entry_good_510⟩, ⟨row_511, good_511, entry_good_511⟩, trivial⟩
