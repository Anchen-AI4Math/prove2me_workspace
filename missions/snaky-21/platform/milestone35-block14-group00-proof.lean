import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 448 = data_448 ∧ Good (rowAt 448) ∧ EntryGood 448) ∧ (rowAt 449 = data_449 ∧ Good (rowAt 449) ∧ EntryGood 449) ∧ (rowAt 450 = data_450 ∧ Good (rowAt 450) ∧ EntryGood 450) ∧ (rowAt 451 = data_451 ∧ Good (rowAt 451) ∧ EntryGood 451) ∧ (rowAt 452 = data_452 ∧ Good (rowAt 452) ∧ EntryGood 452) ∧ (rowAt 453 = data_453 ∧ Good (rowAt 453) ∧ EntryGood 453) ∧ (rowAt 454 = data_454 ∧ Good (rowAt 454) ∧ EntryGood 454) ∧ (rowAt 455 = data_455 ∧ Good (rowAt 455) ∧ EntryGood 455) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group00_piece01_correct.2.2.2.1, trivial⟩
