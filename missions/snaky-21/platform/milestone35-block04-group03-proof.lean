import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152) ∧ (rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153) ∧ (rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154) ∧ (rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155) ∧ (rowAt 156 = data_156 ∧ Good (rowAt 156) ∧ EntryGood 156) ∧ (rowAt 157 = data_157 ∧ Good (rowAt 157) ∧ EntryGood 157) ∧ (rowAt 158 = data_158 ∧ Good (rowAt 158) ∧ EntryGood 158) ∧ (rowAt 159 = data_159 ∧ Good (rowAt 159) ∧ EntryGood 159) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group03_piece01_correct.2.2.2.1, trivial⟩
