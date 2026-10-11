import Definitions.Def_Snaky35Cache18
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group00_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_28 (j : ℕ) (hj : j < 20) : entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_2 : rowAt 2 = data_2 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.1).1
theorem row_64 : rowAt 64 = data_64 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_293 : rowAt 293 = data_293 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_355 : rowAt 355 = data_355 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.1).1
theorem row_364 : rowAt 364 = data_364 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_382 : rowAt 382 = data_382 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_385 : rowAt 385 = data_385 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.1).1
theorem row_390 : rowAt 390 = data_390 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.1).1
theorem row_407 : rowAt 407 = data_407 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_442 : rowAt 442 = data_442 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_462 : rowAt 462 = data_462 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_465 : rowAt 465 = data_465 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_495 : rowAt 495 = data_495 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_497 : rowAt 497 = data_497 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_499 : rowAt 499 = data_499 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_504 : rowAt 504 = data_504 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_518 : rowAt 518 = data_518 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.1).1
theorem row_527 : rowAt 527 = data_527 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_531 : rowAt 531 = data_531 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_539 : rowAt 539 = data_539 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_540 : rowAt 540 = data_540 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_544 : rowAt 544 = data_544 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.1).1
theorem row_556 : rowAt 556 = data_556 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_559 : rowAt 559 = data_559 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_563 : rowAt 563 = data_563 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_564 : rowAt 564 = data_564 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_570 : rowAt 570 = data_570 := (OAI.SnakyCertificate.MilestoneChecks.block17_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_574 : rowAt 574 = data_574 := (OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece00_correct.2.2.2.1).1
theorem entry_575_checked : entryAt 575 = entry_575 := by
  rw [entry_chunk_28 9 (by decide)]
  decide +kernel
theorem row_575 : rowAt 575 = data_575 := by
  rw [rowAt, dif_neg (by decide : ¬ 575 < 6), entry_575_checked]
  change forkRow [placeRow ⟨314, 4, 5, 4⟩ (rowAt 314), placeRow ⟨504, 4, 5, 3⟩ (rowAt 504), placeRow ⟨180, 4, 4, 5⟩ (rowAt 180), placeRow ⟨442, 4, 4, 5⟩ (rowAt 442), placeRow ⟨559, 0, 4, 5⟩ (rowAt 559)] = data_575
  rw [row_314, row_504, row_180, row_442, row_559]
  apply row_ext <;> decide +kernel
theorem entry_good_575 : EntryGood 575 := by
  unfold EntryGood
  rw [entry_575_checked]
  decide +kernel
theorem good_575 : Good (rowAt 575) := by
  rw [row_575]
  unfold Good
  decide +kernel

theorem entry_576_checked : entryAt 576 = entry_576 := by
  rw [entry_chunk_28 10 (by decide)]
  decide +kernel
theorem row_576 : rowAt 576 = data_576 := by
  rw [rowAt, dif_neg (by decide : ¬ 576 < 6), entry_576_checked]
  change forkRow [placeRow ⟨495, 0, 5, 4⟩ (rowAt 495), placeRow ⟨544, 4, 5, 4⟩ (rowAt 544), placeRow ⟨462, 3, 3, 5⟩ (rowAt 462), placeRow ⟨540, 0, 3, 6⟩ (rowAt 540), placeRow ⟨355, 4, 5, 4⟩ (rowAt 355), placeRow ⟨539, 0, 3, 6⟩ (rowAt 539), placeRow ⟨497, 4, 5, 4⟩ (rowAt 497), placeRow ⟨390, 1, 5, 4⟩ (rowAt 390), placeRow ⟨563, 0, 2, 4⟩ (rowAt 563), placeRow ⟨518, 4, 5, 4⟩ (rowAt 518)] = data_576
  rw [row_495, row_544, row_462, row_540, row_355, row_539, row_497, row_390, row_563, row_518]
  apply row_ext <;> decide +kernel
theorem entry_good_576 : EntryGood 576 := by
  unfold EntryGood
  rw [entry_576_checked]
  decide +kernel
theorem good_576 : Good (rowAt 576) := by
  rw [row_576]
  unfold Good
  decide +kernel

theorem entry_577_checked : entryAt 577 = entry_577 := by
  rw [entry_chunk_28 11 (by decide)]
  decide +kernel
theorem row_577 : rowAt 577 = data_577 := by
  rw [rowAt, dif_neg (by decide : ¬ 577 < 6), entry_577_checked]
  change forkRow [placeRow ⟨64, 7, 5, 4⟩ (rowAt 64), placeRow ⟨64, 1, 3, 1⟩ (rowAt 64), placeRow ⟨443, 1, 5, 4⟩ (rowAt 443), placeRow ⟨443, 7, 3, 1⟩ (rowAt 443)] = data_577
  rw [row_64, row_443]
  apply row_ext <;> decide +kernel
theorem entry_good_577 : EntryGood 577 := by
  unfold EntryGood
  rw [entry_577_checked]
  decide +kernel
theorem good_577 : Good (rowAt 577) := by
  rw [row_577]
  unfold Good
  decide +kernel

theorem entry_578_checked : entryAt 578 = entry_578 := by
  rw [entry_chunk_28 12 (by decide)]
  decide +kernel
theorem row_578 : rowAt 578 = data_578 := by
  rw [rowAt, dif_neg (by decide : ¬ 578 < 6), entry_578_checked]
  change forkRow [placeRow ⟨574, 4, 4, 5⟩ (rowAt 574), placeRow ⟨2, 1, 4, 3⟩ (rowAt 2)] = data_578
  rw [row_574, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_578 : EntryGood 578 := by
  unfold EntryGood
  rw [entry_578_checked]
  decide +kernel
theorem good_578 : Good (rowAt 578) := by
  rw [row_578]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 575 = data_575 ∧ Good (rowAt 575) ∧ EntryGood 575) ∧ (rowAt 576 = data_576 ∧ Good (rowAt 576) ∧ EntryGood 576) ∧ (rowAt 577 = data_577 ∧ Good (rowAt 577) ∧ EntryGood 577) ∧ (rowAt 578 = data_578 ∧ Good (rowAt 578) ∧ EntryGood 578) ∧ True := by
  exact ⟨⟨row_575, good_575, entry_good_575⟩, ⟨row_576, good_576, entry_good_576⟩, ⟨row_577, good_577, entry_good_577⟩, ⟨row_578, good_578, entry_good_578⟩, trivial⟩
