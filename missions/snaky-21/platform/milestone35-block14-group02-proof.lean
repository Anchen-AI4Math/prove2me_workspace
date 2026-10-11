import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block14_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 464 = data_464 ∧ Good (rowAt 464) ∧ EntryGood 464) ∧ (rowAt 465 = data_465 ∧ Good (rowAt 465) ∧ EntryGood 465) ∧ (rowAt 466 = data_466 ∧ Good (rowAt 466) ∧ EntryGood 466) ∧ (rowAt 467 = data_467 ∧ Good (rowAt 467) ∧ EntryGood 467) ∧ (rowAt 468 = data_468 ∧ Good (rowAt 468) ∧ EntryGood 468) ∧ (rowAt 469 = data_469 ∧ Good (rowAt 469) ∧ EntryGood 469) ∧ (rowAt 470 = data_470 ∧ Good (rowAt 470) ∧ EntryGood 470) ∧ (rowAt 471 = data_471 ∧ Good (rowAt 471) ∧ EntryGood 471) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group02_piece01_correct.2.2.2.1, trivial⟩
