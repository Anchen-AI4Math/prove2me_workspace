import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 416 = data_416 ∧ Good (rowAt 416) ∧ EntryGood 416) ∧ (rowAt 417 = data_417 ∧ Good (rowAt 417) ∧ EntryGood 417) ∧ (rowAt 418 = data_418 ∧ Good (rowAt 418) ∧ EntryGood 418) ∧ (rowAt 419 = data_419 ∧ Good (rowAt 419) ∧ EntryGood 419) ∧ (rowAt 420 = data_420 ∧ Good (rowAt 420) ∧ EntryGood 420) ∧ (rowAt 421 = data_421 ∧ Good (rowAt 421) ∧ EntryGood 421) ∧ (rowAt 422 = data_422 ∧ Good (rowAt 422) ∧ EntryGood 422) ∧ (rowAt 423 = data_423 ∧ Good (rowAt 423) ∧ EntryGood 423) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group00_piece01_correct.2.2.2.1, trivial⟩
