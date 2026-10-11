import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 408 = data_408 ∧ Good (rowAt 408) ∧ EntryGood 408) ∧ (rowAt 409 = data_409 ∧ Good (rowAt 409) ∧ EntryGood 409) ∧ (rowAt 410 = data_410 ∧ Good (rowAt 410) ∧ EntryGood 410) ∧ (rowAt 411 = data_411 ∧ Good (rowAt 411) ∧ EntryGood 411) ∧ (rowAt 412 = data_412 ∧ Good (rowAt 412) ∧ EntryGood 412) ∧ (rowAt 413 = data_413 ∧ Good (rowAt 413) ∧ EntryGood 413) ∧ (rowAt 414 = data_414 ∧ Good (rowAt 414) ∧ EntryGood 414) ∧ (rowAt 415 = data_415 ∧ Good (rowAt 415) ∧ EntryGood 415) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group03_piece01_correct.2.2.2.1, trivial⟩
