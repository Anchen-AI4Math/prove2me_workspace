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
theorem entry_560_checked : entryAt 560 = entry_560 := by
  rw [entry_chunk_27 14 (by decide)]
  decide +kernel
theorem row_560 : rowAt 560 = data_560 := by
  rw [rowAt, dif_neg (by decide : ¬ 560 < 6), entry_560_checked]
  change forkRow [placeRow ⟨517, 5, 5, 4⟩ (rowAt 517), placeRow ⟨416, 5, 4, 3⟩ (rowAt 416), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359), placeRow ⟨356, 6, 3, 4⟩ (rowAt 356), placeRow ⟨483, 0, 4, 6⟩ (rowAt 483)] = data_560
  rw [row_517, row_416, row_359, row_356, row_483]
  apply row_ext <;> decide +kernel
theorem entry_good_560 : EntryGood 560 := by
  unfold EntryGood
  rw [entry_560_checked]
  decide +kernel
theorem good_560 : Good (rowAt 560) := by
  rw [row_560]
  unfold Good
  decide +kernel

theorem entry_561_checked : entryAt 561 = entry_561 := by
  rw [entry_chunk_27 15 (by decide)]
  decide +kernel
theorem row_561 : rowAt 561 = data_561 := by
  rw [rowAt, dif_neg (by decide : ¬ 561 < 6), entry_561_checked]
  change forkRow [placeRow ⟨295, 0, 5, 4⟩ (rowAt 295), placeRow ⟨173, 2, 5, 4⟩ (rowAt 173), placeRow ⟨263, 6, 1, 4⟩ (rowAt 263), placeRow ⟨236, 1, 5, 5⟩ (rowAt 236), placeRow ⟨546, 4, 5, 4⟩ (rowAt 546), placeRow ⟨176, 2, 5, 4⟩ (rowAt 176), placeRow ⟨535, 0, 4, 5⟩ (rowAt 535)] = data_561
  rw [row_295, row_173, row_263, row_236, row_546, row_176, row_535]
  apply row_ext <;> decide +kernel
theorem entry_good_561 : EntryGood 561 := by
  unfold EntryGood
  rw [entry_561_checked]
  decide +kernel
theorem good_561 : Good (rowAt 561) := by
  rw [row_561]
  unfold Good
  decide +kernel

theorem entry_562_checked : entryAt 562 = entry_562 := by
  rw [entry_chunk_27 16 (by decide)]
  decide +kernel
theorem row_562 : rowAt 562 = data_562 := by
  rw [rowAt, dif_neg (by decide : ¬ 562 < 6), entry_562_checked]
  change forkRow [placeRow ⟨6, 7, 3, 0⟩ (rowAt 6), placeRow ⟨559, 0, 4, 5⟩ (rowAt 559)] = data_562
  rw [row_6, row_559]
  apply row_ext <;> decide +kernel
theorem entry_good_562 : EntryGood 562 := by
  unfold EntryGood
  rw [entry_562_checked]
  decide +kernel
theorem good_562 : Good (rowAt 562) := by
  rw [row_562]
  unfold Good
  decide +kernel

theorem entry_563_checked : entryAt 563 = entry_563 := by
  rw [entry_chunk_27 17 (by decide)]
  decide +kernel
theorem row_563 : rowAt 563 = data_563 := by
  rw [rowAt, dif_neg (by decide : ¬ 563 < 6), entry_563_checked]
  change forkRow [placeRow ⟨167, 0, 7, 4⟩ (rowAt 167), placeRow ⟨538, 0, 3, 4⟩ (rowAt 538), placeRow ⟨514, 0, 7, 4⟩ (rowAt 514), placeRow ⟨330, 4, 3, 4⟩ (rowAt 330), placeRow ⟨545, 0, 5, 5⟩ (rowAt 545)] = data_563
  rw [row_167, row_538, row_514, row_330, row_545]
  apply row_ext <;> decide +kernel
theorem entry_good_563 : EntryGood 563 := by
  unfold EntryGood
  rw [entry_563_checked]
  decide +kernel
theorem good_563 : Good (rowAt 563) := by
  rw [row_563]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 560 = data_560 ∧ Good (rowAt 560) ∧ EntryGood 560) ∧ (rowAt 561 = data_561 ∧ Good (rowAt 561) ∧ EntryGood 561) ∧ (rowAt 562 = data_562 ∧ Good (rowAt 562) ∧ EntryGood 562) ∧ (rowAt 563 = data_563 ∧ Good (rowAt 563) ∧ EntryGood 563) ∧ True := by
  exact ⟨⟨row_560, good_560, entry_good_560⟩, ⟨row_561, good_561, entry_good_561⟩, ⟨row_562, good_562, entry_good_562⟩, ⟨row_563, good_563, entry_good_563⟩, trivial⟩
