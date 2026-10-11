import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 128 = data_128 ∧ Good (rowAt 128) ∧ EntryGood 128) ∧ (rowAt 129 = data_129 ∧ Good (rowAt 129) ∧ EntryGood 129) ∧ (rowAt 130 = data_130 ∧ Good (rowAt 130) ∧ EntryGood 130) ∧ (rowAt 131 = data_131 ∧ Good (rowAt 131) ∧ EntryGood 131) ∧ (rowAt 132 = data_132 ∧ Good (rowAt 132) ∧ EntryGood 132) ∧ (rowAt 133 = data_133 ∧ Good (rowAt 133) ∧ EntryGood 133) ∧ (rowAt 134 = data_134 ∧ Good (rowAt 134) ∧ EntryGood 134) ∧ (rowAt 135 = data_135 ∧ Good (rowAt 135) ∧ EntryGood 135) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group00_piece01_correct.2.2.2.1, trivial⟩
