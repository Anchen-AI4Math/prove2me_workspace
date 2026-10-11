import Definitions.Def_Snaky35Cache14
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_chunk_lookups
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group01_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group02_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_chunk_23 (j : ℕ) (hj : j < 20) : entryAt (466 + j) = tableChunk_23[j]?.getD emptyEntry := (chunk_lookups.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) j hj
theorem row_0 : rowAt 0 = data_0 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.1).1
theorem row_6 : rowAt 6 = data_6 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.1).1
theorem row_25 : rowAt 25 = data_25 := (OAI.SnakyCertificate.MilestoneChecks.block00_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_55 : rowAt 55 = data_55 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_63 : rowAt 63 = data_63 := (OAI.SnakyCertificate.MilestoneChecks.block01_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_70 : rowAt 70 = data_70 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.1).1
theorem row_83 : rowAt 83 = data_83 := (OAI.SnakyCertificate.MilestoneChecks.block02_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_121 : rowAt 121 = data_121 := (OAI.SnakyCertificate.MilestoneChecks.block03_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_154 : rowAt 154 = data_154 := (OAI.SnakyCertificate.MilestoneChecks.block04_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_165 : rowAt 165 = data_165 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.1).1
theorem row_190 : rowAt 190 = data_190 := (OAI.SnakyCertificate.MilestoneChecks.block05_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_261 : rowAt 261 = data_261 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.1).1
theorem row_269 : rowAt 269 = data_269 := (OAI.SnakyCertificate.MilestoneChecks.block08_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_436 : rowAt 436 = data_436 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_443 : rowAt 443 = data_443 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_445 : rowAt 445 = data_445 := (OAI.SnakyCertificate.MilestoneChecks.block13_correct.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1).1
theorem row_457 : rowAt 457 = data_457 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_correct.2.1).1
theorem row_463 : rowAt 463 = data_463 := (OAI.SnakyCertificate.MilestoneChecks.block14_group01_correct.2.2.2.2.2.2.2.1).1
theorem row_466 : rowAt 466 = data_466 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_correct.2.2.1).1
theorem row_471 : rowAt 471 = data_471 := (OAI.SnakyCertificate.MilestoneChecks.block14_group02_correct.2.2.2.2.2.2.2.1).1
theorem entry_472_checked : entryAt 472 = entry_472 := by
  rw [entry_chunk_23 6 (by decide)]
  decide +kernel
theorem row_472 : rowAt 472 = data_472 := by
  rw [rowAt, dif_neg (by decide : ¬ 472 < 6), entry_472_checked]
  change forkRow [placeRow ⟨6, 5, 5, 0⟩ (rowAt 6), placeRow ⟨466, 0, 6, 3⟩ (rowAt 466)] = data_472
  rw [row_6, row_466]
  apply row_ext <;> decide +kernel
theorem entry_good_472 : EntryGood 472 := by
  unfold EntryGood
  rw [entry_472_checked]
  decide +kernel
theorem good_472 : Good (rowAt 472) := by
  rw [row_472]
  unfold Good
  decide +kernel

theorem entry_473_checked : entryAt 473 = entry_473 := by
  rw [entry_chunk_23 7 (by decide)]
  decide +kernel
theorem row_473 : rowAt 473 = data_473 := by
  rw [rowAt, dif_neg (by decide : ¬ 473 < 6), entry_473_checked]
  change forkRow [placeRow ⟨121, 5, 5, 4⟩ (rowAt 121), placeRow ⟨436, 0, 3, 7⟩ (rowAt 436), placeRow ⟨445, 4, 5, 4⟩ (rowAt 445)] = data_473
  rw [row_121, row_436, row_445]
  apply row_ext <;> decide +kernel
theorem entry_good_473 : EntryGood 473 := by
  unfold EntryGood
  rw [entry_473_checked]
  decide +kernel
theorem good_473 : Good (rowAt 473) := by
  rw [row_473]
  unfold Good
  decide +kernel

theorem entry_474_checked : entryAt 474 = entry_474 := by
  rw [entry_chunk_23 8 (by decide)]
  decide +kernel
theorem row_474 : rowAt 474 = data_474 := by
  rw [rowAt, dif_neg (by decide : ¬ 474 < 6), entry_474_checked]
  change forkRow [placeRow ⟨463, 0, 6, 5⟩ (rowAt 463), placeRow ⟨70, 0, 3, 5⟩ (rowAt 70), placeRow ⟨83, 1, 5, 3⟩ (rowAt 83)] = data_474
  rw [row_463, row_70, row_83]
  apply row_ext <;> decide +kernel
theorem entry_good_474 : EntryGood 474 := by
  unfold EntryGood
  rw [entry_474_checked]
  decide +kernel
theorem good_474 : Good (rowAt 474) := by
  rw [row_474]
  unfold Good
  decide +kernel

theorem entry_475_checked : entryAt 475 = entry_475 := by
  rw [entry_chunk_23 9 (by decide)]
  decide +kernel
theorem row_475 : rowAt 475 = data_475 := by
  rw [rowAt, dif_neg (by decide : ¬ 475 < 6), entry_475_checked]
  change forkRow [placeRow ⟨63, 1, 5, 3⟩ (rowAt 63), placeRow ⟨261, 1, 4, 3⟩ (rowAt 261), placeRow ⟨457, 0, 2, 5⟩ (rowAt 457), placeRow ⟨269, 2, 2, 5⟩ (rowAt 269)] = data_475
  rw [row_63, row_261, row_457, row_269]
  apply row_ext <;> decide +kernel
theorem entry_good_475 : EntryGood 475 := by
  unfold EntryGood
  rw [entry_475_checked]
  decide +kernel
theorem good_475 : Good (rowAt 475) := by
  rw [row_475]
  unfold Good
  decide +kernel


end OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 472 = data_472 ∧ Good (rowAt 472) ∧ EntryGood 472) ∧ (rowAt 473 = data_473 ∧ Good (rowAt 473) ∧ EntryGood 473) ∧ (rowAt 474 = data_474 ∧ Good (rowAt 474) ∧ EntryGood 474) ∧ (rowAt 475 = data_475 ∧ Good (rowAt 475) ∧ EntryGood 475) ∧ True := by
  exact ⟨⟨row_472, good_472, entry_good_472⟩, ⟨row_473, good_473, entry_good_473⟩, ⟨row_474, good_474, entry_good_474⟩, ⟨row_475, good_475, entry_good_475⟩, trivial⟩
