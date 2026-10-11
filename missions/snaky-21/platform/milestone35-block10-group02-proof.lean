import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 336 = data_336 ∧ Good (rowAt 336) ∧ EntryGood 336) ∧ (rowAt 337 = data_337 ∧ Good (rowAt 337) ∧ EntryGood 337) ∧ (rowAt 338 = data_338 ∧ Good (rowAt 338) ∧ EntryGood 338) ∧ (rowAt 339 = data_339 ∧ Good (rowAt 339) ∧ EntryGood 339) ∧ (rowAt 340 = data_340 ∧ Good (rowAt 340) ∧ EntryGood 340) ∧ (rowAt 341 = data_341 ∧ Good (rowAt 341) ∧ EntryGood 341) ∧ (rowAt 342 = data_342 ∧ Good (rowAt 342) ∧ EntryGood 342) ∧ (rowAt 343 = data_343 ∧ Good (rowAt 343) ∧ EntryGood 343) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group02_piece01_correct.2.2.2.1, trivial⟩
