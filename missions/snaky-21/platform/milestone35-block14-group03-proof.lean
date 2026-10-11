import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 472 = data_472 ∧ Good (rowAt 472) ∧ EntryGood 472) ∧ (rowAt 473 = data_473 ∧ Good (rowAt 473) ∧ EntryGood 473) ∧ (rowAt 474 = data_474 ∧ Good (rowAt 474) ∧ EntryGood 474) ∧ (rowAt 475 = data_475 ∧ Good (rowAt 475) ∧ EntryGood 475) ∧ (rowAt 476 = data_476 ∧ Good (rowAt 476) ∧ EntryGood 476) ∧ (rowAt 477 = data_477 ∧ Good (rowAt 477) ∧ EntryGood 477) ∧ (rowAt 478 = data_478 ∧ Good (rowAt 478) ∧ EntryGood 478) ∧ (rowAt 479 = data_479 ∧ Good (rowAt 479) ∧ EntryGood 479) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group03_piece01_correct.2.2.2.1, trivial⟩
