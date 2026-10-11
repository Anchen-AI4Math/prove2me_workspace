import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 256 = data_256 ∧ Good (rowAt 256) ∧ EntryGood 256) ∧ (rowAt 257 = data_257 ∧ Good (rowAt 257) ∧ EntryGood 257) ∧ (rowAt 258 = data_258 ∧ Good (rowAt 258) ∧ EntryGood 258) ∧ (rowAt 259 = data_259 ∧ Good (rowAt 259) ∧ EntryGood 259) ∧ (rowAt 260 = data_260 ∧ Good (rowAt 260) ∧ EntryGood 260) ∧ (rowAt 261 = data_261 ∧ Good (rowAt 261) ∧ EntryGood 261) ∧ (rowAt 262 = data_262 ∧ Good (rowAt 262) ∧ EntryGood 262) ∧ (rowAt 263 = data_263 ∧ Good (rowAt 263) ∧ EntryGood 263) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group00_piece01_correct.2.2.2.1, trivial⟩
