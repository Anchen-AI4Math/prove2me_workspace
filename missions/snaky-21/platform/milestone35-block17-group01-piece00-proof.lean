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
theorem entry_552_checked : entryAt 552 = entry_552 := by
  rw [entry_chunk_27 6 (by decide)]
  decide +kernel
theorem row_552 : rowAt 552 = data_552 := by
  rw [rowAt, dif_neg (by decide : ¬ 552 < 6), entry_552_checked]
  change forkRow [placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨504, 1, 3, 3⟩ (rowAt 504), placeRow ⟨404, 5, 2, 3⟩ (rowAt 404)] = data_552
  rw [row_443, row_64, row_504, row_404]
  apply row_ext <;> decide +kernel
theorem entry_good_552 : EntryGood 552 := by
  unfold EntryGood
  rw [entry_552_checked]
  decide +kernel
theorem good_552 : Good (rowAt 552) := by
  rw [row_552]
  unfold Good
  decide +kernel

theorem entry_553_checked : entryAt 553 = entry_553 := by
  rw [entry_chunk_27 7 (by decide)]
  decide +kernel
theorem row_553 : rowAt 553 = data_553 := by
  rw [rowAt, dif_neg (by decide : ¬ 553 < 6), entry_553_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 4, 5, 4⟩ (rowAt 261), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180)] = data_553
  rw [row_63, row_261, row_471, row_442, row_504, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_553 : EntryGood 553 := by
  unfold EntryGood
  rw [entry_553_checked]
  decide +kernel
theorem good_553 : Good (rowAt 553) := by
  rw [row_553]
  unfold Good
  decide +kernel

theorem entry_554_checked : entryAt 554 = entry_554 := by
  rw [entry_chunk_27 8 (by decide)]
  decide +kernel
theorem row_554 : rowAt 554 = data_554 := by
  rw [rowAt, dif_neg (by decide : ¬ 554 < 6), entry_554_checked]
  change forkRow [placeRow ⟨30, 6, 5, 4⟩ (rowAt 30), placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨474, 0, 4, 5⟩ (rowAt 474)] = data_554
  rw [row_30, row_96, row_474]
  apply row_ext <;> decide +kernel
theorem entry_good_554 : EntryGood 554 := by
  unfold EntryGood
  rw [entry_554_checked]
  decide +kernel
theorem good_554 : Good (rowAt 554) := by
  rw [row_554]
  unfold Good
  decide +kernel

theorem entry_555_checked : entryAt 555 = entry_555 := by
  rw [entry_chunk_27 9 (by decide)]
  decide +kernel
theorem row_555 : rowAt 555 = data_555 := by
  rw [rowAt, dif_neg (by decide : ¬ 555 < 6), entry_555_checked]
  change forkRow [placeRow ⟨504, 5, 3, 5⟩ (rowAt 504), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨471, 1, 1, 5⟩ (rowAt 471)] = data_555
  rw [row_504, row_513, row_55, row_443, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_555 : EntryGood 555 := by
  unfold EntryGood
  rw [entry_555_checked]
  decide +kernel
theorem good_555 : Good (rowAt 555) := by
  rw [row_555]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 552 = data_552 ∧ Good (rowAt 552) ∧ EntryGood 552) ∧ (rowAt 553 = data_553 ∧ Good (rowAt 553) ∧ EntryGood 553) ∧ (rowAt 554 = data_554 ∧ Good (rowAt 554) ∧ EntryGood 554) ∧ (rowAt 555 = data_555 ∧ Good (rowAt 555) ∧ EntryGood 555) ∧ True := by
  exact ⟨⟨row_552, good_552, entry_good_552⟩, ⟨row_553, good_553, entry_good_553⟩, ⟨row_554, good_554, entry_good_554⟩, ⟨row_555, good_555, entry_good_555⟩, trivial⟩
