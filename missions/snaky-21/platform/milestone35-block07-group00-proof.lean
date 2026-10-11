import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block07_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 224 = data_224 ∧ Good (rowAt 224) ∧ EntryGood 224) ∧ (rowAt 225 = data_225 ∧ Good (rowAt 225) ∧ EntryGood 225) ∧ (rowAt 226 = data_226 ∧ Good (rowAt 226) ∧ EntryGood 226) ∧ (rowAt 227 = data_227 ∧ Good (rowAt 227) ∧ EntryGood 227) ∧ (rowAt 228 = data_228 ∧ Good (rowAt 228) ∧ EntryGood 228) ∧ (rowAt 229 = data_229 ∧ Good (rowAt 229) ∧ EntryGood 229) ∧ (rowAt 230 = data_230 ∧ Good (rowAt 230) ∧ EntryGood 230) ∧ (rowAt 231 = data_231 ∧ Good (rowAt 231) ∧ EntryGood 231) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group00_piece01_correct.2.2.2.1, trivial⟩
