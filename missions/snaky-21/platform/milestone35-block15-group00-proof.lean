import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block15_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 480 = data_480 ∧ Good (rowAt 480) ∧ EntryGood 480) ∧ (rowAt 481 = data_481 ∧ Good (rowAt 481) ∧ EntryGood 481) ∧ (rowAt 482 = data_482 ∧ Good (rowAt 482) ∧ EntryGood 482) ∧ (rowAt 483 = data_483 ∧ Good (rowAt 483) ∧ EntryGood 483) ∧ (rowAt 484 = data_484 ∧ Good (rowAt 484) ∧ EntryGood 484) ∧ (rowAt 485 = data_485 ∧ Good (rowAt 485) ∧ EntryGood 485) ∧ (rowAt 486 = data_486 ∧ Good (rowAt 486) ∧ EntryGood 486) ∧ (rowAt 487 = data_487 ∧ Good (rowAt 487) ∧ EntryGood 487) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group00_piece01_correct.2.2.2.1, trivial⟩
