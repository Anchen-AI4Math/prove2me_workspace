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
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group01_piece00_correct
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
theorem row_582 : rowAt 582 = data_582 := (OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece00_correct.2.2.2.1).1
theorem entry_583_checked : entryAt 583 = entry_583 := by
  rw [entry_chunk_28 17 (by decide)]
  decide +kernel
theorem row_583 : rowAt 583 = data_583 := by
  rw [rowAt, dif_neg (by decide : ¬ 583 < 6), entry_583_checked]
  change forkRow [placeRow ⟨25, 5, 4, 3⟩ (rowAt 25), placeRow ⟨525, 0, 5, 4⟩ (rowAt 525), placeRow ⟨582, 0, 2, 8⟩ (rowAt 582), placeRow ⟨221, 3, 3, 7⟩ (rowAt 221)] = data_583
  rw [row_25, row_525, row_582, row_221]
  apply row_ext <;> decide +kernel
theorem entry_good_583 : EntryGood 583 := by
  unfold EntryGood
  rw [entry_583_checked]
  decide +kernel
theorem good_583 : Good (rowAt 583) := by
  rw [row_583]
  unfold Good
  decide +kernel

theorem entry_584_checked : entryAt 584 = entry_584 := by
  rw [entry_chunk_28 18 (by decide)]
  decide +kernel
theorem row_584 : rowAt 584 = data_584 := by
  rw [rowAt, dif_neg (by decide : ¬ 584 < 6), entry_584_checked]
  change forkRow [placeRow ⟨263, 1, 4, 5⟩ (rowAt 263), placeRow ⟨236, 4, 3, 5⟩ (rowAt 236), placeRow ⟨548, 3, 3, 4⟩ (rowAt 548), placeRow ⟨295, 3, 4, 5⟩ (rowAt 295), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨173, 1, 4, 5⟩ (rowAt 173)] = data_584
  rw [row_263, row_236, row_548, row_295, row_577, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_584 : EntryGood 584 := by
  unfold EntryGood
  rw [entry_584_checked]
  decide +kernel
theorem good_584 : Good (rowAt 584) := by
  rw [row_584]
  unfold Good
  decide +kernel

theorem entry_585_checked : entryAt 585 = entry_585 := by
  rw [entry_chunk_28 19 (by decide)]
  decide +kernel
theorem row_585 : rowAt 585 = data_585 := by
  rw [rowAt, dif_neg (by decide : ¬ 585 < 6), entry_585_checked]
  change forkRow [placeRow ⟨236, 2, 5, 1⟩ (rowAt 236), placeRow ⟨300, 4, 4, 5⟩ (rowAt 300), placeRow ⟨479, 1, 4, 5⟩ (rowAt 479), placeRow ⟨577, 0, 4, 5⟩ (rowAt 577), placeRow ⟨183, 3, 4, 5⟩ (rowAt 183), placeRow ⟨527, 6, 5, 1⟩ (rowAt 527)] = data_585
  rw [row_236, row_300, row_479, row_577, row_183, row_527]
  apply row_ext <;> decide +kernel
theorem entry_good_585 : EntryGood 585 := by
  unfold EntryGood
  rw [entry_585_checked]
  decide +kernel
theorem good_585 : Good (rowAt 585) := by
  rw [row_585]
  unfold Good
  decide +kernel

theorem entry_586_checked : entryAt 586 = entry_586 := by
  rw [entry_chunk_29 0 (by decide)]
  decide +kernel
theorem row_586 : rowAt 586 = data_586 := by
  rw [rowAt, dif_neg (by decide : ¬ 586 < 6), entry_586_checked]
  change forkRow [placeRow ⟨465, 4, 4, 5⟩ (rowAt 465), placeRow ⟨558, 1, 4, 5⟩ (rowAt 558), placeRow ⟨385, 1, 4, 5⟩ (rowAt 385), placeRow ⟨379, 4, 4, 5⟩ (rowAt 379), placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨469, 2, 4, 5⟩ (rowAt 469), placeRow ⟨467, 2, 4, 5⟩ (rowAt 467), placeRow ⟨527, 4, 5, 5⟩ (rowAt 527), placeRow ⟨553, 0, 4, 5⟩ (rowAt 553), placeRow ⟨552, 1, 4, 5⟩ (rowAt 552), placeRow ⟨555, 1, 4, 5⟩ (rowAt 555), placeRow ⟨564, 0, 6, 4⟩ (rowAt 564), placeRow ⟨583, 0, 5, 2⟩ (rowAt 583)] = data_586
  rw [row_465, row_558, row_385, row_379, row_524, row_469, row_467, row_527, row_553, row_552, row_555, row_564, row_583]
  apply row_ext <;> decide +kernel
theorem entry_good_586 : EntryGood 586 := by
  unfold EntryGood
  rw [entry_586_checked]
  decide +kernel
theorem good_586 : Good (rowAt 586) := by
  rw [row_586]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 583 = data_583 ∧ Good (rowAt 583) ∧ EntryGood 583) ∧ (rowAt 584 = data_584 ∧ Good (rowAt 584) ∧ EntryGood 584) ∧ (rowAt 585 = data_585 ∧ Good (rowAt 585) ∧ EntryGood 585) ∧ (rowAt 586 = data_586 ∧ Good (rowAt 586) ∧ EntryGood 586) ∧ True := by
  exact ⟨⟨row_583, good_583, entry_good_583⟩, ⟨row_584, good_584, entry_good_584⟩, ⟨row_585, good_585, entry_good_585⟩, ⟨row_586, good_586, entry_good_586⟩, trivial⟩
