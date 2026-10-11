import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block16_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 512 = data_512 ∧ Good (rowAt 512) ∧ EntryGood 512) ∧ (rowAt 513 = data_513 ∧ Good (rowAt 513) ∧ EntryGood 513) ∧ (rowAt 514 = data_514 ∧ Good (rowAt 514) ∧ EntryGood 514) ∧ (rowAt 515 = data_515 ∧ Good (rowAt 515) ∧ EntryGood 515) ∧ (rowAt 516 = data_516 ∧ Good (rowAt 516) ∧ EntryGood 516) ∧ (rowAt 517 = data_517 ∧ Good (rowAt 517) ∧ EntryGood 517) ∧ (rowAt 518 = data_518 ∧ Good (rowAt 518) ∧ EntryGood 518) ∧ (rowAt 519 = data_519 ∧ Good (rowAt 519) ∧ EntryGood 519) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group00_piece01_correct.2.2.2.1, trivial⟩
