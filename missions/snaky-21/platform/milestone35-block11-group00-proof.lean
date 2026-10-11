import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block11_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 352 = data_352 ∧ Good (rowAt 352) ∧ EntryGood 352) ∧ (rowAt 353 = data_353 ∧ Good (rowAt 353) ∧ EntryGood 353) ∧ (rowAt 354 = data_354 ∧ Good (rowAt 354) ∧ EntryGood 354) ∧ (rowAt 355 = data_355 ∧ Good (rowAt 355) ∧ EntryGood 355) ∧ (rowAt 356 = data_356 ∧ Good (rowAt 356) ∧ EntryGood 356) ∧ (rowAt 357 = data_357 ∧ Good (rowAt 357) ∧ EntryGood 357) ∧ (rowAt 358 = data_358 ∧ Good (rowAt 358) ∧ EntryGood 358) ∧ (rowAt 359 = data_359 ∧ Good (rowAt 359) ∧ EntryGood 359) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group00_piece01_correct.2.2.2.1, trivial⟩
