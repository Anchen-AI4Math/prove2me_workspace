import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block03_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 104 = data_104 ∧ Good (rowAt 104) ∧ EntryGood 104) ∧ (rowAt 105 = data_105 ∧ Good (rowAt 105) ∧ EntryGood 105) ∧ (rowAt 106 = data_106 ∧ Good (rowAt 106) ∧ EntryGood 106) ∧ (rowAt 107 = data_107 ∧ Good (rowAt 107) ∧ EntryGood 107) ∧ (rowAt 108 = data_108 ∧ Good (rowAt 108) ∧ EntryGood 108) ∧ (rowAt 109 = data_109 ∧ Good (rowAt 109) ∧ EntryGood 109) ∧ (rowAt 110 = data_110 ∧ Good (rowAt 110) ∧ EntryGood 110) ∧ (rowAt 111 = data_111 ∧ Good (rowAt 111) ∧ EntryGood 111) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group01_piece01_correct.2.2.2.1, trivial⟩
