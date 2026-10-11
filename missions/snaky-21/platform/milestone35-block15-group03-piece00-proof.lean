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
theorem entry_504_checked : entryAt 504 = entry_504 := by
  rw [entry_chunk_24 18 (by decide)]
  decide +kernel
theorem row_504 : rowAt 504 = data_504 := by
  rw [rowAt, dif_neg (by decide : ¬ 504 < 6), entry_504_checked]
  change forkRow [placeRow ⟨381, 0, 3, 4⟩ (rowAt 381), placeRow ⟨310, 4, 4, 5⟩ (rowAt 310), placeRow ⟨159, 0, 5, 6⟩ (rowAt 159), placeRow ⟨351, 4, 3, 4⟩ (rowAt 351), placeRow ⟨496, 0, 3, 4⟩ (rowAt 496)] = data_504
  rw [row_381, row_310, row_159, row_351, row_496]
  apply row_ext <;> decide +kernel
theorem entry_good_504 : EntryGood 504 := by
  unfold EntryGood
  rw [entry_504_checked]
  decide +kernel
theorem good_504 : Good (rowAt 504) := by
  rw [row_504]
  unfold Good
  decide +kernel

theorem entry_505_checked : entryAt 505 = entry_505 := by
  rw [entry_chunk_24 19 (by decide)]
  decide +kernel
theorem row_505 : rowAt 505 = data_505 := by
  rw [rowAt, dif_neg (by decide : ¬ 505 < 6), entry_505_checked]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨499, 0, 5, 4⟩ (rowAt 499), placeRow ⟨183, 1, 4, 5⟩ (rowAt 183), placeRow ⟨282, 1, 4, 5⟩ (rowAt 282)] = data_505
  rw [row_173, row_499, row_183, row_282]
  apply row_ext <;> decide +kernel
theorem entry_good_505 : EntryGood 505 := by
  unfold EntryGood
  rw [entry_505_checked]
  decide +kernel
theorem good_505 : Good (rowAt 505) := by
  rw [row_505]
  unfold Good
  decide +kernel

theorem entry_506_checked : entryAt 506 = entry_506 := by
  rw [entry_chunk_25 0 (by decide)]
  decide +kernel
theorem row_506 : rowAt 506 = data_506 := by
  rw [rowAt, dif_neg (by decide : ¬ 506 < 6), entry_506_checked]
  change forkRow [placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨200, 7, 1, 4⟩ (rowAt 200), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173)] = data_506
  rw [row_99, row_200, row_318, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_506 : EntryGood 506 := by
  unfold EntryGood
  rw [entry_506_checked]
  decide +kernel
theorem good_506 : Good (rowAt 506) := by
  rw [row_506]
  unfold Good
  decide +kernel

theorem entry_507_checked : entryAt 507 = entry_507 := by
  rw [entry_chunk_25 1 (by decide)]
  decide +kernel
theorem row_507 : rowAt 507 = data_507 := by
  rw [rowAt, dif_neg (by decide : ¬ 507 < 6), entry_507_checked]
  change forkRow [placeRow ⟨151, 0, 2, 4⟩ (rowAt 151), placeRow ⟨33, 3, 4, 3⟩ (rowAt 33), placeRow ⟨481, 0, 5, 4⟩ (rowAt 481)] = data_507
  rw [row_151, row_33, row_481]
  apply row_ext <;> decide +kernel
theorem entry_good_507 : EntryGood 507 := by
  unfold EntryGood
  rw [entry_507_checked]
  decide +kernel
theorem good_507 : Good (rowAt 507) := by
  rw [row_507]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 504 = data_504 ∧ Good (rowAt 504) ∧ EntryGood 504) ∧ (rowAt 505 = data_505 ∧ Good (rowAt 505) ∧ EntryGood 505) ∧ (rowAt 506 = data_506 ∧ Good (rowAt 506) ∧ EntryGood 506) ∧ (rowAt 507 = data_507 ∧ Good (rowAt 507) ∧ EntryGood 507) ∧ True := by
  exact ⟨⟨row_504, good_504, entry_good_504⟩, ⟨row_505, good_505, entry_good_505⟩, ⟨row_506, good_506, entry_good_506⟩, ⟨row_507, good_507, entry_good_507⟩, trivial⟩
