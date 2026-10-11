import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block04_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 136 = data_136 ∧ Good (rowAt 136) ∧ EntryGood 136) ∧ (rowAt 137 = data_137 ∧ Good (rowAt 137) ∧ EntryGood 137) ∧ (rowAt 138 = data_138 ∧ Good (rowAt 138) ∧ EntryGood 138) ∧ (rowAt 139 = data_139 ∧ Good (rowAt 139) ∧ EntryGood 139) ∧ (rowAt 140 = data_140 ∧ Good (rowAt 140) ∧ EntryGood 140) ∧ (rowAt 141 = data_141 ∧ Good (rowAt 141) ∧ EntryGood 141) ∧ (rowAt 142 = data_142 ∧ Good (rowAt 142) ∧ EntryGood 142) ∧ (rowAt 143 = data_143 ∧ Good (rowAt 143) ∧ EntryGood 143) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group01_piece01_correct.2.2.2.1, trivial⟩
