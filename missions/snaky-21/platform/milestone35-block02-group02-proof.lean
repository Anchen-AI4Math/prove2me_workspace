import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 80 = data_80 ∧ Good (rowAt 80) ∧ EntryGood 80) ∧ (rowAt 81 = data_81 ∧ Good (rowAt 81) ∧ EntryGood 81) ∧ (rowAt 82 = data_82 ∧ Good (rowAt 82) ∧ EntryGood 82) ∧ (rowAt 83 = data_83 ∧ Good (rowAt 83) ∧ EntryGood 83) ∧ (rowAt 84 = data_84 ∧ Good (rowAt 84) ∧ EntryGood 84) ∧ (rowAt 85 = data_85 ∧ Good (rowAt 85) ∧ EntryGood 85) ∧ (rowAt 86 = data_86 ∧ Good (rowAt 86) ∧ EntryGood 86) ∧ (rowAt 87 = data_87 ∧ Good (rowAt 87) ∧ EntryGood 87) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group02_piece01_correct.2.2.2.1, trivial⟩
