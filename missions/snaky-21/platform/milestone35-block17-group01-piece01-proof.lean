import Definitions.Def_Snaky35Cache17
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_27 (j : ℕ) (hj : j < 20) : entryAt (546 + j) = tableChunk_27[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_7 : rowAt 7 = data_7 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.1).1
theorem row_30 : rowAt 30 = data_30 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_34 : rowAt 34 = data_34 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_96 : rowAt 96 = data_96 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.1).1
theorem row_155 : rowAt 155 = data_155 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_228 : rowAt 228 = data_228 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_404 : rowAt 404 = data_404 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_406 : rowAt 406 = data_406 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_411 : rowAt 411 = data_411 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_442 : rowAt 442 = data_442 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_460 : rowAt 460 = data_460 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_471 : rowAt 471 = data_471 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_474 : rowAt 474 = data_474 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_504 : rowAt 504 = data_504 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_513 : rowAt 513 = data_513 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.1).1
theorem row_531 : rowAt 531 = data_531 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_538 : rowAt 538 = data_538 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_549 : rowAt 549 = data_549 := (OAI.SnakyCertificate.MilestoneChecks.block17_group00_correct.2.2.2.2.2.1).1
theorem entry_556_checked : entryAt 556 = entry_556 := by
  rw [entry_chunk_27 10 (by decide)]
  decide +kernel
theorem row_556 : rowAt 556 = data_556 := by
  rw [rowAt, dif_neg (by decide : ¬ 556 < 6), entry_556_checked]
  change forkRow [placeRow ⟨34, 1, 4, 2⟩ (rowAt 34), placeRow ⟨549, 0, 3, 4⟩ (rowAt 549)] = data_556
  rw [row_34, row_549]
  apply row_ext <;> decide +kernel
theorem entry_good_556 : EntryGood 556 := by
  unfold EntryGood
  rw [entry_556_checked]
  decide +kernel
theorem good_556 : Good (rowAt 556) := by
  rw [row_556]
  unfold Good
  decide +kernel

theorem entry_557_checked : entryAt 557 = entry_557 := by
  rw [entry_chunk_27 11 (by decide)]
  decide +kernel
theorem row_557 : rowAt 557 = data_557 := by
  rw [rowAt, dif_neg (by decide : ¬ 557 < 6), entry_557_checked]
  change forkRow [placeRow ⟨460, 0, 5, 4⟩ (rowAt 460), placeRow ⟨460, 4, 2, 4⟩ (rowAt 460), placeRow ⟨460, 2, 5, 4⟩ (rowAt 460), placeRow ⟨411, 4, 5, 4⟩ (rowAt 411), placeRow ⟨531, 0, 3, 6⟩ (rowAt 531), placeRow ⟨531, 4, 4, 6⟩ (rowAt 531), placeRow ⟨406, 5, 5, 4⟩ (rowAt 406)] = data_557
  rw [row_460, row_411, row_531, row_406]
  apply row_ext <;> decide +kernel
theorem entry_good_557 : EntryGood 557 := by
  unfold EntryGood
  rw [entry_557_checked]
  decide +kernel
theorem good_557 : Good (rowAt 557) := by
  rw [row_557]
  unfold Good
  decide +kernel

theorem entry_558_checked : entryAt 558 = entry_558 := by
  rw [entry_chunk_27 12 (by decide)]
  decide +kernel
theorem row_558 : rowAt 558 = data_558 := by
  rw [rowAt, dif_neg (by decide : ¬ 558 < 6), entry_558_checked]
  change forkRow [placeRow ⟨180, 5, 5, 4⟩ (rowAt 180), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨442, 1, 5, 4⟩ (rowAt 442)] = data_558
  rw [row_180, row_443, row_513, row_442]
  apply row_ext <;> decide +kernel
theorem entry_good_558 : EntryGood 558 := by
  unfold EntryGood
  rw [entry_558_checked]
  decide +kernel
theorem good_558 : Good (rowAt 558) := by
  rw [row_558]
  unfold Good
  decide +kernel

theorem entry_559_checked : entryAt 559 = entry_559 := by
  rw [entry_chunk_27 13 (by decide)]
  decide +kernel
theorem row_559 : rowAt 559 = data_559 := by
  rw [rowAt, dif_neg (by decide : ¬ 559 < 6), entry_559_checked]
  change forkRow [placeRow ⟨228, 4, 5, 2⟩ (rowAt 228), placeRow ⟨7, 3, 3, 4⟩ (rowAt 7), placeRow ⟨155, 4, 4, 5⟩ (rowAt 155), placeRow ⟨538, 5, 4, 5⟩ (rowAt 538)] = data_559
  rw [row_228, row_7, row_155, row_538]
  apply row_ext <;> decide +kernel
theorem entry_good_559 : EntryGood 559 := by
  unfold EntryGood
  rw [entry_559_checked]
  decide +kernel
theorem good_559 : Good (rowAt 559) := by
  rw [row_559]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 556 = data_556 ∧ Good (rowAt 556) ∧ EntryGood 556) ∧ (rowAt 557 = data_557 ∧ Good (rowAt 557) ∧ EntryGood 557) ∧ (rowAt 558 = data_558 ∧ Good (rowAt 558) ∧ EntryGood 558) ∧ (rowAt 559 = data_559 ∧ Good (rowAt 559) ∧ EntryGood 559) ∧ True := by
  exact ⟨⟨row_556, good_556, entry_good_556⟩, ⟨row_557, good_557, entry_good_557⟩, ⟨row_558, good_558, entry_good_558⟩, ⟨row_559, good_559, entry_good_559⟩, trivial⟩
