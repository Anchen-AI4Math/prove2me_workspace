import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block02_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 64 = data_64 ∧ Good (rowAt 64) ∧ EntryGood 64) ∧ (rowAt 65 = data_65 ∧ Good (rowAt 65) ∧ EntryGood 65) ∧ (rowAt 66 = data_66 ∧ Good (rowAt 66) ∧ EntryGood 66) ∧ (rowAt 67 = data_67 ∧ Good (rowAt 67) ∧ EntryGood 67) ∧ (rowAt 68 = data_68 ∧ Good (rowAt 68) ∧ EntryGood 68) ∧ (rowAt 69 = data_69 ∧ Good (rowAt 69) ∧ EntryGood 69) ∧ (rowAt 70 = data_70 ∧ Good (rowAt 70) ∧ EntryGood 70) ∧ (rowAt 71 = data_71 ∧ Good (rowAt 71) ∧ EntryGood 71) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group00_piece01_correct.2.2.2.1, trivial⟩
