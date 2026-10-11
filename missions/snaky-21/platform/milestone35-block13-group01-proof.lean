import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block13_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 424 = data_424 ∧ Good (rowAt 424) ∧ EntryGood 424) ∧ (rowAt 425 = data_425 ∧ Good (rowAt 425) ∧ EntryGood 425) ∧ (rowAt 426 = data_426 ∧ Good (rowAt 426) ∧ EntryGood 426) ∧ (rowAt 427 = data_427 ∧ Good (rowAt 427) ∧ EntryGood 427) ∧ (rowAt 428 = data_428 ∧ Good (rowAt 428) ∧ EntryGood 428) ∧ (rowAt 429 = data_429 ∧ Good (rowAt 429) ∧ EntryGood 429) ∧ (rowAt 430 = data_430 ∧ Good (rowAt 430) ∧ EntryGood 430) ∧ (rowAt 431 = data_431 ∧ Good (rowAt 431) ∧ EntryGood 431) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group01_piece01_correct.2.2.2.1, trivial⟩
