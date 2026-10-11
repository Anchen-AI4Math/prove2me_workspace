import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block10_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 344 = data_344 ∧ Good (rowAt 344) ∧ EntryGood 344) ∧ (rowAt 345 = data_345 ∧ Good (rowAt 345) ∧ EntryGood 345) ∧ (rowAt 346 = data_346 ∧ Good (rowAt 346) ∧ EntryGood 346) ∧ (rowAt 347 = data_347 ∧ Good (rowAt 347) ∧ EntryGood 347) ∧ (rowAt 348 = data_348 ∧ Good (rowAt 348) ∧ EntryGood 348) ∧ (rowAt 349 = data_349 ∧ Good (rowAt 349) ∧ EntryGood 349) ∧ (rowAt 350 = data_350 ∧ Good (rowAt 350) ∧ EntryGood 350) ∧ (rowAt 351 = data_351 ∧ Good (rowAt 351) ∧ EntryGood 351) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group03_piece01_correct.2.2.2.1, trivial⟩
