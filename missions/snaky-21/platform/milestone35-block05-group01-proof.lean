import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 168 = data_168 ∧ Good (rowAt 168) ∧ EntryGood 168) ∧ (rowAt 169 = data_169 ∧ Good (rowAt 169) ∧ EntryGood 169) ∧ (rowAt 170 = data_170 ∧ Good (rowAt 170) ∧ EntryGood 170) ∧ (rowAt 171 = data_171 ∧ Good (rowAt 171) ∧ EntryGood 171) ∧ (rowAt 172 = data_172 ∧ Good (rowAt 172) ∧ EntryGood 172) ∧ (rowAt 173 = data_173 ∧ Good (rowAt 173) ∧ EntryGood 173) ∧ (rowAt 174 = data_174 ∧ Good (rowAt 174) ∧ EntryGood 174) ∧ (rowAt 175 = data_175 ∧ Good (rowAt 175) ∧ EntryGood 175) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group01_piece01_correct.2.2.2.1, trivial⟩
