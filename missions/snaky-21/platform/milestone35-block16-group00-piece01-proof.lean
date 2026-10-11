import Definitions.Def_Snaky35Cache16
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group00_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_25 (j : ℕ) (hj : j < 20) : entryAt (506 + j) = tableChunk_25[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_9 : rowAt 9 = data_9 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_10 : rowAt 10 = data_10 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_38 : rowAt 38 = data_38 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.1).1
theorem row_57 : rowAt 57 = data_57 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_62 : rowAt 62 = data_62 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_107 : rowAt 107 = data_107 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_140 : rowAt 140 = data_140 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_193 : rowAt 193 = data_193 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.1).1
theorem row_244 : rowAt 244 = data_244 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_311 : rowAt 311 = data_311 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_329 : rowAt 329 = data_329 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_396 : rowAt 396 = data_396 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_408 : rowAt 408 = data_408 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_496 : rowAt 496 = data_496 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_498 : rowAt 498 = data_498 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_506 : rowAt 506 = data_506 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_507 : rowAt 507 = data_507 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_510 : rowAt 510 = data_510 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_514 : rowAt 514 = data_514 := (OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece00_correct.2.2.1).1
theorem entry_516_checked : entryAt 516 = entry_516 := by
  rw [entry_chunk_25 10 (by decide)]
  decide +kernel
theorem row_516 : rowAt 516 = data_516 := by
  rw [rowAt, dif_neg (by decide : ¬ 516 < 6), entry_516_checked]
  change forkRow [placeRow ⟨329, 0, 4, 3⟩ (rowAt 329), placeRow ⟨244, 4, 2, 4⟩ (rowAt 244), placeRow ⟨10, 1, 4, 5⟩ (rowAt 10), placeRow ⟨506, 4, 2, 4⟩ (rowAt 506)] = data_516
  rw [row_329, row_244, row_10, row_506]
  apply row_ext <;> decide +kernel
theorem entry_good_516 : EntryGood 516 := by
  unfold EntryGood
  rw [entry_516_checked]
  decide +kernel
theorem good_516 : Good (rowAt 516) := by
  rw [row_516]
  unfold Good
  decide +kernel

theorem entry_517_checked : entryAt 517 = entry_517 := by
  rw [entry_chunk_25 11 (by decide)]
  decide +kernel
theorem row_517 : rowAt 517 = data_517 := by
  rw [rowAt, dif_neg (by decide : ¬ 517 < 6), entry_517_checked]
  change forkRow [placeRow ⟨496, 0, 2, 3⟩ (rowAt 496), placeRow ⟨140, 0, 4, 2⟩ (rowAt 140), placeRow ⟨193, 1, 4, 2⟩ (rowAt 193)] = data_517
  rw [row_496, row_140, row_193]
  apply row_ext <;> decide +kernel
theorem entry_good_517 : EntryGood 517 := by
  unfold EntryGood
  rw [entry_517_checked]
  decide +kernel
theorem good_517 : Good (rowAt 517) := by
  rw [row_517]
  unfold Good
  decide +kernel

theorem entry_518_checked : entryAt 518 = entry_518 := by
  rw [entry_chunk_25 12 (by decide)]
  decide +kernel
theorem row_518 : rowAt 518 = data_518 := by
  rw [rowAt, dif_neg (by decide : ¬ 518 < 6), entry_518_checked]
  change forkRow [placeRow ⟨9, 6, 3, 4⟩ (rowAt 9), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514)] = data_518
  rw [row_9, row_514]
  apply row_ext <;> decide +kernel
theorem entry_good_518 : EntryGood 518 := by
  unfold EntryGood
  rw [entry_518_checked]
  decide +kernel
theorem good_518 : Good (rowAt 518) := by
  rw [row_518]
  unfold Good
  decide +kernel

theorem entry_519_checked : entryAt 519 = entry_519 := by
  rw [entry_chunk_25 13 (by decide)]
  decide +kernel
theorem row_519 : rowAt 519 = data_519 := by
  rw [rowAt, dif_neg (by decide : ¬ 519 < 6), entry_519_checked]
  change forkRow [placeRow ⟨498, 0, 4, 3⟩ (rowAt 498), placeRow ⟨311, 4, 3, 4⟩ (rowAt 311), placeRow ⟨38, 1, 4, 5⟩ (rowAt 38), placeRow ⟨408, 0, 3, 4⟩ (rowAt 408)] = data_519
  rw [row_498, row_311, row_38, row_408]
  apply row_ext <;> decide +kernel
theorem entry_good_519 : EntryGood 519 := by
  unfold EntryGood
  rw [entry_519_checked]
  decide +kernel
theorem good_519 : Good (rowAt 519) := by
  rw [row_519]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 516 = data_516 ∧ Good (rowAt 516) ∧ EntryGood 516) ∧ (rowAt 517 = data_517 ∧ Good (rowAt 517) ∧ EntryGood 517) ∧ (rowAt 518 = data_518 ∧ Good (rowAt 518) ∧ EntryGood 518) ∧ (rowAt 519 = data_519 ∧ Good (rowAt 519) ∧ EntryGood 519) ∧ True := by
  exact ⟨⟨row_516, good_516, entry_good_516⟩, ⟨row_517, good_517, entry_good_517⟩, ⟨row_518, good_518, entry_good_518⟩, ⟨row_519, good_519, entry_good_519⟩, trivial⟩
