import Definitions.Def_Snaky35Cache17
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block17_group02_piece00_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_27 (j : ℕ) (hj : j < 20) : entryAt (546 + j) = tableChunk_27[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem entry_chunk_28 (j : ℕ) (hj : j < 20) : entryAt (566 + j) = tableChunk_28[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_21 : rowAt 21 = data_21 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_131 : rowAt 131 = data_131 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.1).1
theorem row_144 : rowAt 144 = data_144 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_167 : rowAt 167 = data_167 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.1).1
theorem row_173 : rowAt 173 = data_173 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_176 : rowAt 176 = data_176 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_180 : rowAt 180 = data_180 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_236 : rowAt 236 = data_236 := (OAI.SnakyCertificate.MilestoneChecks.block07_correct.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_263 : rowAt 263 = data_263 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.1).1
theorem row_295 : rowAt 295 = data_295 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.1).1
theorem row_314 : rowAt 314 = data_314 := (OAI.SnakyCertificate.MilestoneChecks.block09_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_330 : rowAt 330 = data_330 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_336 : rowAt 336 = data_336 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_340 : rowAt 340 = data_340 := (OAI.SnakyCertificate.MilestoneChecks.block10_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_356 : rowAt 356 = data_356 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.1).1
theorem row_359 : rowAt 359 = data_359 := (OAI.SnakyCertificate.MilestoneChecks.block11_correct.2.2.2.2.2.2.2.1).1
theorem row_401 : rowAt 401 = data_401 := (OAI.SnakyCertificate.MilestoneChecks.block12_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_416 : rowAt 416 = data_416 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.1).1
theorem row_421 : rowAt 421 = data_421 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.1).1
theorem row_423 : rowAt 423 = data_423 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.1).1
theorem row_425 : rowAt 425 = data_425 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.1).1
theorem row_442 : rowAt 442 = data_442 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_459 : rowAt 459 = data_459 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_466 : rowAt 466 = data_466 := (OAI.SnakyCertificate.MilestoneChecks.block14_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_483 : rowAt 483 = data_483 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.1).1
theorem row_500 : rowAt 500 = data_500 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_504 : rowAt 504 = data_504 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_509 : rowAt 509 = data_509 := (OAI.SnakyCertificate.MilestoneChecks.block15_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_514 : rowAt 514 = data_514 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.1).1
theorem row_517 : rowAt 517 = data_517 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.1).1
theorem row_528 : rowAt 528 = data_528 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_535 : rowAt 535 = data_535 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_538 : rowAt 538 = data_538 := (OAI.SnakyCertificate.MilestoneChecks.block16_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_545 : rowAt 545 = data_545 := (OAI.SnakyCertificate.MilestoneChecks.block17_group00_correct.2.1).1
theorem row_546 : rowAt 546 = data_546 := (OAI.SnakyCertificate.MilestoneChecks.block17_group00_correct.2.2.1).1
theorem row_559 : rowAt 559 = data_559 := (OAI.SnakyCertificate.MilestoneChecks.block17_group01_correct.2.2.2.2.2.2.2.1).1
theorem row_560 : rowAt 560 = data_560 := (OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.1).1
theorem row_561 : rowAt 561 = data_561 := (OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.2.1).1
theorem entry_564_checked : entryAt 564 = entry_564 := by
  rw [entry_chunk_27 18 (by decide)]
  decide +kernel
theorem row_564 : rowAt 564 = data_564 := by
  rw [rowAt, dif_neg (by decide : ¬ 564 < 6), entry_564_checked]
  change forkRow [placeRow ⟨560, 0, 4, 3⟩ (rowAt 560), placeRow ⟨421, 0, 3, 4⟩ (rowAt 421), placeRow ⟨401, 1, 3, 4⟩ (rowAt 401), placeRow ⟨340, 3, 3, 4⟩ (rowAt 340), placeRow ⟨509, 0, 3, 4⟩ (rowAt 509), placeRow ⟨528, 0, 4, 3⟩ (rowAt 528), placeRow ⟨423, 5, 4, 3⟩ (rowAt 423), placeRow ⟨425, 5, 4, 3⟩ (rowAt 425), placeRow ⟨336, 0, 3, 4⟩ (rowAt 336)] = data_564
  rw [row_560, row_421, row_401, row_340, row_509, row_528, row_423, row_425, row_336]
  apply row_ext <;> decide +kernel
theorem entry_good_564 : EntryGood 564 := by
  unfold EntryGood
  rw [entry_564_checked]
  decide +kernel
theorem good_564 : Good (rowAt 564) := by
  rw [row_564]
  unfold Good
  decide +kernel

theorem entry_565_checked : entryAt 565 = entry_565 := by
  rw [entry_chunk_27 19 (by decide)]
  decide +kernel
theorem row_565 : rowAt 565 = data_565 := by
  rw [rowAt, dif_neg (by decide : ¬ 565 < 6), entry_565_checked]
  change forkRow [placeRow ⟨443, 4, 4, 5⟩ (rowAt 443), placeRow ⟨131, 3, 3, 4⟩ (rowAt 131), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨459, 0, 5, 5⟩ (rowAt 459), placeRow ⟨144, 4, 3, 4⟩ (rowAt 144)] = data_565
  rw [row_443, row_131, row_538, row_459, row_144]
  apply row_ext <;> decide +kernel
theorem entry_good_565 : EntryGood 565 := by
  unfold EntryGood
  rw [entry_565_checked]
  decide +kernel
theorem good_565 : Good (rowAt 565) := by
  rw [row_565]
  unfold Good
  decide +kernel

theorem entry_566_checked : entryAt 566 = entry_566 := by
  rw [entry_chunk_28 0 (by decide)]
  decide +kernel
theorem row_566 : rowAt 566 = data_566 := by
  rw [rowAt, dif_neg (by decide : ¬ 566 < 6), entry_566_checked]
  change forkRow [placeRow ⟨314, 0, 3, 4⟩ (rowAt 314), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504)] = data_566
  rw [row_314, row_180, row_442, row_466, row_504]
  apply row_ext <;> decide +kernel
theorem entry_good_566 : EntryGood 566 := by
  unfold EntryGood
  rw [entry_566_checked]
  decide +kernel
theorem good_566 : Good (rowAt 566) := by
  rw [row_566]
  unfold Good
  decide +kernel

theorem entry_567_checked : entryAt 567 = entry_567 := by
  rw [entry_chunk_28 1 (by decide)]
  decide +kernel
theorem row_567 : rowAt 567 = data_567 := by
  rw [rowAt, dif_neg (by decide : ¬ 567 < 6), entry_567_checked]
  change forkRow [placeRow ⟨21, 1, 4, 3⟩ (rowAt 21), placeRow ⟨561, 0, 6, 4⟩ (rowAt 561), placeRow ⟨500, 4, 3, 1⟩ (rowAt 500)] = data_567
  rw [row_21, row_561, row_500]
  apply row_ext <;> decide +kernel
theorem entry_good_567 : EntryGood 567 := by
  unfold EntryGood
  rw [entry_567_checked]
  decide +kernel
theorem good_567 : Good (rowAt 567) := by
  rw [row_567]
  unfold Good
  decide +kernel

end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 564 = data_564 ∧ Good (rowAt 564) ∧ EntryGood 564) ∧ (rowAt 565 = data_565 ∧ Good (rowAt 565) ∧ EntryGood 565) ∧ (rowAt 566 = data_566 ∧ Good (rowAt 566) ∧ EntryGood 566) ∧ (rowAt 567 = data_567 ∧ Good (rowAt 567) ∧ EntryGood 567) ∧ True := by
  exact ⟨⟨row_564, good_564, entry_good_564⟩, ⟨row_565, good_565, entry_good_565⟩, ⟨row_566, good_566, entry_good_566⟩, ⟨row_567, good_567, entry_good_567⟩, trivial⟩
