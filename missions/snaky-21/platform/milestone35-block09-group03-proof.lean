import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 312 = data_312 ∧ Good (rowAt 312) ∧ EntryGood 312) ∧ (rowAt 313 = data_313 ∧ Good (rowAt 313) ∧ EntryGood 313) ∧ (rowAt 314 = data_314 ∧ Good (rowAt 314) ∧ EntryGood 314) ∧ (rowAt 315 = data_315 ∧ Good (rowAt 315) ∧ EntryGood 315) ∧ (rowAt 316 = data_316 ∧ Good (rowAt 316) ∧ EntryGood 316) ∧ (rowAt 317 = data_317 ∧ Good (rowAt 317) ∧ EntryGood 317) ∧ (rowAt 318 = data_318 ∧ Good (rowAt 318) ∧ EntryGood 318) ∧ (rowAt 319 = data_319 ∧ Good (rowAt 319) ∧ EntryGood 319) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group03_piece01_correct.2.2.2.1, trivial⟩
