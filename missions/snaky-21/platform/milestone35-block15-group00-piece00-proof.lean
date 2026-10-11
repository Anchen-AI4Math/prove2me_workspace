import Definitions.Def_Snaky35Cache15
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_23 (j : ℕ) (hj : j < 20) : entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_24 (j : ℕ) (hj : j < 20) : entryAt (486 + j) = tableChunk_24[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_4 : rowAt 4 = data_4 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_108 : rowAt 108 = data_108 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_163 : rowAt 163 = data_163 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.1).1
theorem row_169 : rowAt 169 = data_169 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_192 : rowAt 192 = data_192 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.1).1
theorem row_206 : rowAt 206 = data_206 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_207 : rowAt 207 = data_207 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_218 : rowAt 218 = data_218 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_292 : rowAt 292 = data_292 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.1).1
theorem row_303 : rowAt 303 = data_303 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_309 : rowAt 309 = data_309 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_319 : rowAt 319 = data_319 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_349 : rowAt 349 = data_349 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_429 : rowAt 429 = data_429 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_475 : rowAt 475 = data_475 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem entry_480_checked : entryAt 480 = entry_480 := by
  rw [entry_chunk_23 14 (by decide)]
  decide +kernel
theorem row_480 : rowAt 480 = data_480 := by
  rw [rowAt, dif_neg (by decide : ¬ 480 < 6), entry_480_checked]
  change forkRow [placeRow ⟨108, 1, 4, 5⟩ (rowAt 108), placeRow ⟨4, 1, 5, 4⟩ (rowAt 4)] = data_480
  rw [row_108, row_4]
  apply row_ext <;> decide +kernel
theorem entry_good_480 : EntryGood 480 := by
  unfold EntryGood
  rw [entry_480_checked]
  decide +kernel
theorem good_480 : Good (rowAt 480) := by
  rw [row_480]
  unfold Good
  decide +kernel

theorem entry_481_checked : entryAt 481 = entry_481 := by
  rw [entry_chunk_23 15 (by decide)]
  decide +kernel
theorem row_481 : rowAt 481 = data_481 := by
  rw [rowAt, dif_neg (by decide : ¬ 481 < 6), entry_481_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨429, 2, 1, 4⟩ (rowAt 429), placeRow ⟨309, 1, 1, 4⟩ (rowAt 309), placeRow ⟨206, 2, 1, 4⟩ (rowAt 206), placeRow ⟨169, 2, 1, 4⟩ (rowAt 169), placeRow ⟨207, 2, 1, 4⟩ (rowAt 207)] = data_481
  rw [row_303, row_429, row_309, row_206, row_169, row_207]
  apply row_ext <;> decide +kernel
theorem entry_good_481 : EntryGood 481 := by
  unfold EntryGood
  rw [entry_481_checked]
  decide +kernel
theorem good_481 : Good (rowAt 481) := by
  rw [row_481]
  unfold Good
  decide +kernel

theorem entry_482_checked : entryAt 482 = entry_482 := by
  rw [entry_chunk_23 16 (by decide)]
  decide +kernel
theorem row_482 : rowAt 482 = data_482 := by
  rw [rowAt, dif_neg (by decide : ¬ 482 < 6), entry_482_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨218, 2, 4, 3⟩ (rowAt 218)] = data_482
  rw [row_6, row_218]
  apply row_ext <;> decide +kernel
theorem entry_good_482 : EntryGood 482 := by
  unfold EntryGood
  rw [entry_482_checked]
  decide +kernel
theorem good_482 : Good (rowAt 482) := by
  rw [row_482]
  unfold Good
  decide +kernel

theorem entry_483_checked : entryAt 483 = entry_483 := by
  rw [entry_chunk_23 17 (by decide)]
  decide +kernel
theorem row_483 : rowAt 483 = data_483 := by
  rw [rowAt, dif_neg (by decide : ¬ 483 < 6), entry_483_checked]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨292, 7, 3, 1⟩ (rowAt 292), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319), placeRow ⟨192, 6, 4, 1⟩ (rowAt 192), placeRow ⟨475, 1, 4, 5⟩ (rowAt 475)] = data_483
  rw [row_173, row_292, row_319, row_192, row_475]
  apply row_ext <;> decide +kernel
theorem entry_good_483 : EntryGood 483 := by
  unfold EntryGood
  rw [entry_483_checked]
  decide +kernel
theorem good_483 : Good (rowAt 483) := by
  rw [row_483]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 480 = data_480 ∧ Good (rowAt 480) ∧ EntryGood 480) ∧ (rowAt 481 = data_481 ∧ Good (rowAt 481) ∧ EntryGood 481) ∧ (rowAt 482 = data_482 ∧ Good (rowAt 482) ∧ EntryGood 482) ∧ (rowAt 483 = data_483 ∧ Good (rowAt 483) ∧ EntryGood 483) ∧ True := by
  exact ⟨⟨row_480, good_480, entry_good_480⟩, ⟨row_481, good_481, entry_good_481⟩, ⟨row_482, good_482, entry_good_482⟩, ⟨row_483, good_483, entry_good_483⟩, trivial⟩
