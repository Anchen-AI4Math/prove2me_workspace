import Definitions.Def_Snaky35Cache18
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_28 (j : ℕ) (hj : j < 20) : entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_29 (j : ℕ) (hj : j < 20) : entryAt (586 + j) = tableChunk_29[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_40 : rowAt 40 = data_40 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_183 : rowAt 183 = data_183 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_221 : rowAt 221 = data_221 := (OAI.SnakyCertificate.MilestoneChecks.block06_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_300 : rowAt 300 = data_300 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_379 : rowAt 379 = data_379 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_385 : rowAt 385 = data_385 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.1).1
theorem row_446 : rowAt 446 = data_446 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_465 : rowAt 465 = data_465 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_467 : rowAt 467 = data_467 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_469 : rowAt 469 = data_469 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_479 : rowAt 479 = data_479 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_480 : rowAt 480 = data_480 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.1).1
theorem row_523 : rowAt 523 = data_523 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_524 : rowAt 524 = data_524 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_525 : rowAt 525 = data_525 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_527 : rowAt 527 = data_527 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_548 : rowAt 548 = data_548 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.1).1
theorem row_552 : rowAt 552 = data_552 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.1).1
theorem row_553 : rowAt 553 = data_553 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_555 : rowAt 555 = data_555 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_558 : rowAt 558 = data_558 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_564 : rowAt 564 = data_564 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_567 : rowAt 567 = data_567 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_576 : rowAt 576 = data_576 := (OAI.SnakyCertificate.MilestoneChecks.block18_group00_correct.2.2.2.2.2.1).1
theorem row_577 : rowAt 577 = data_577 := (OAI.SnakyCertificate.MilestoneChecks.block18_group00_correct.2.2.2.2.2.2.1).1
theorem row_578 : rowAt 578 = data_578 := (OAI.SnakyCertificate.MilestoneChecks.block18_group00_correct.2.2.2.2.2.2.2.1).1
theorem entry_579_checked : entryAt 579 = entry_579 := by
  rw [entry_chunk_28 13 (by decide)]
  decide +kernel
theorem row_579 : rowAt 579 = data_579 := by
  rw [rowAt, dif_neg (by decide : ¬ 579 < 6), entry_579_checked]
  change forkRow [placeRow ⟨2, 1, 4, 3⟩ (rowAt 2), placeRow ⟨576, 4, 4, 5⟩ (rowAt 576)] = data_579
  rw [row_2, row_576]
  apply row_ext <;> decide +kernel
theorem entry_good_579 : EntryGood 579 := by
  unfold EntryGood
  rw [entry_579_checked]
  decide +kernel
theorem good_579 : Good (rowAt 579) := by
  rw [row_579]
  unfold Good
  decide +kernel

theorem entry_580_checked : entryAt 580 = entry_580 := by
  rw [entry_chunk_28 14 (by decide)]
  decide +kernel
theorem row_580 : rowAt 580 = data_580 := by
  rw [rowAt, dif_neg (by decide : ¬ 580 < 6), entry_580_checked]
  change forkRow [placeRow ⟨2, 7, 4, 2⟩ (rowAt 2), placeRow ⟨579, 0, 3, 3⟩ (rowAt 579)] = data_580
  rw [row_2, row_579]
  apply row_ext <;> decide +kernel
theorem entry_good_580 : EntryGood 580 := by
  unfold EntryGood
  rw [entry_580_checked]
  decide +kernel
theorem good_580 : Good (rowAt 580) := by
  rw [row_580]
  unfold Good
  decide +kernel

theorem entry_581_checked : entryAt 581 = entry_581 := by
  rw [entry_chunk_28 15 (by decide)]
  decide +kernel
theorem row_581 : rowAt 581 = data_581 := by
  rw [rowAt, dif_neg (by decide : ¬ 581 < 6), entry_581_checked]
  change forkRow [placeRow ⟨578, 4, 5, 3⟩ (rowAt 578), placeRow ⟨2, 5, 4, 2⟩ (rowAt 2)] = data_581
  rw [row_578, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_581 : EntryGood 581 := by
  unfold EntryGood
  rw [entry_581_checked]
  decide +kernel
theorem good_581 : Good (rowAt 581) := by
  rw [row_581]
  unfold Good
  decide +kernel

theorem entry_582_checked : entryAt 582 = entry_582 := by
  rw [entry_chunk_28 16 (by decide)]
  decide +kernel
theorem row_582 : rowAt 582 = data_582 := by
  rw [rowAt, dif_neg (by decide : ¬ 582 < 6), entry_582_checked]
  change forkRow [placeRow ⟨40, 3, 4, 3⟩ (rowAt 40), placeRow ⟨446, 5, 5, 3⟩ (rowAt 446), placeRow ⟨523, 0, 7, 0⟩ (rowAt 523), placeRow ⟨480, 4, 5, 3⟩ (rowAt 480), placeRow ⟨567, 4, 5, 4⟩ (rowAt 567)] = data_582
  rw [row_40, row_446, row_523, row_480, row_567]
  apply row_ext <;> decide +kernel
theorem entry_good_582 : EntryGood 582 := by
  unfold EntryGood
  rw [entry_582_checked]
  decide +kernel
theorem good_582 : Good (rowAt 582) := by
  rw [row_582]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 579 = data_579 ∧ Good (rowAt 579) ∧ EntryGood 579) ∧ (rowAt 580 = data_580 ∧ Good (rowAt 580) ∧ EntryGood 580) ∧ (rowAt 581 = data_581 ∧ Good (rowAt 581) ∧ EntryGood 581) ∧ (rowAt 582 = data_582 ∧ Good (rowAt 582) ∧ EntryGood 582) ∧ True := by
  exact ⟨⟨row_579, good_579, entry_good_579⟩, ⟨row_580, good_580, entry_good_580⟩, ⟨row_581, good_581, entry_good_581⟩, ⟨row_582, good_582, entry_good_582⟩, trivial⟩
