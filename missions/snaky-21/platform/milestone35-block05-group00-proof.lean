import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 160 = data_160 ∧ Good (rowAt 160) ∧ EntryGood 160) ∧ (rowAt 161 = data_161 ∧ Good (rowAt 161) ∧ EntryGood 161) ∧ (rowAt 162 = data_162 ∧ Good (rowAt 162) ∧ EntryGood 162) ∧ (rowAt 163 = data_163 ∧ Good (rowAt 163) ∧ EntryGood 163) ∧ (rowAt 164 = data_164 ∧ Good (rowAt 164) ∧ EntryGood 164) ∧ (rowAt 165 = data_165 ∧ Good (rowAt 165) ∧ EntryGood 165) ∧ (rowAt 166 = data_166 ∧ Good (rowAt 166) ∧ EntryGood 166) ∧ (rowAt 167 = data_167 ∧ Good (rowAt 167) ∧ EntryGood 167) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group00_piece01_correct.2.2.2.1, trivial⟩
