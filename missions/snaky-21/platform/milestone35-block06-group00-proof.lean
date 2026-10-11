import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 192 = data_192 ∧ Good (rowAt 192) ∧ EntryGood 192) ∧ (rowAt 193 = data_193 ∧ Good (rowAt 193) ∧ EntryGood 193) ∧ (rowAt 194 = data_194 ∧ Good (rowAt 194) ∧ EntryGood 194) ∧ (rowAt 195 = data_195 ∧ Good (rowAt 195) ∧ EntryGood 195) ∧ (rowAt 196 = data_196 ∧ Good (rowAt 196) ∧ EntryGood 196) ∧ (rowAt 197 = data_197 ∧ Good (rowAt 197) ∧ EntryGood 197) ∧ (rowAt 198 = data_198 ∧ Good (rowAt 198) ∧ EntryGood 198) ∧ (rowAt 199 = data_199 ∧ Good (rowAt 199) ∧ EntryGood 199) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group00_piece01_correct.2.2.2.1, trivial⟩
