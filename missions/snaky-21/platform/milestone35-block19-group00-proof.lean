import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block19_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 589 = data_589 ∧ Good (rowAt 589) ∧ EntryGood 589) ∧ (rowAt 590 = data_590 ∧ Good (rowAt 590) ∧ EntryGood 590) ∧ (rowAt 591 = data_591 ∧ Good (rowAt 591) ∧ EntryGood 591) ∧ (rowAt 592 = data_592 ∧ Good (rowAt 592) ∧ EntryGood 592) ∧ (rowAt 593 = data_593 ∧ Good (rowAt 593) ∧ EntryGood 593) ∧ (rowAt 594 = data_594 ∧ Good (rowAt 594) ∧ EntryGood 594) ∧ (rowAt 595 = data_595 ∧ Good (rowAt 595) ∧ EntryGood 595) ∧ (rowAt 596 = data_596 ∧ Good (rowAt 596) ∧ EntryGood 596) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block19_group00_piece01_correct.2.2.2.1, trivial⟩
