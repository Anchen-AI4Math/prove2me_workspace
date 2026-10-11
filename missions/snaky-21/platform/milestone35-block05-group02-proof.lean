import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 176 = data_176 ∧ Good (rowAt 176) ∧ EntryGood 176) ∧ (rowAt 177 = data_177 ∧ Good (rowAt 177) ∧ EntryGood 177) ∧ (rowAt 178 = data_178 ∧ Good (rowAt 178) ∧ EntryGood 178) ∧ (rowAt 179 = data_179 ∧ Good (rowAt 179) ∧ EntryGood 179) ∧ (rowAt 180 = data_180 ∧ Good (rowAt 180) ∧ EntryGood 180) ∧ (rowAt 181 = data_181 ∧ Good (rowAt 181) ∧ EntryGood 181) ∧ (rowAt 182 = data_182 ∧ Good (rowAt 182) ∧ EntryGood 182) ∧ (rowAt 183 = data_183 ∧ Good (rowAt 183) ∧ EntryGood 183) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group02_piece01_correct.2.2.2.1, trivial⟩
