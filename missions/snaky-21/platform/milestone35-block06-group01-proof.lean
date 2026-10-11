import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group01_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group01_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 200 = data_200 ∧ Good (rowAt 200) ∧ EntryGood 200) ∧ (rowAt 201 = data_201 ∧ Good (rowAt 201) ∧ EntryGood 201) ∧ (rowAt 202 = data_202 ∧ Good (rowAt 202) ∧ EntryGood 202) ∧ (rowAt 203 = data_203 ∧ Good (rowAt 203) ∧ EntryGood 203) ∧ (rowAt 204 = data_204 ∧ Good (rowAt 204) ∧ EntryGood 204) ∧ (rowAt 205 = data_205 ∧ Good (rowAt 205) ∧ EntryGood 205) ∧ (rowAt 206 = data_206 ∧ Good (rowAt 206) ∧ EntryGood 206) ∧ (rowAt 207 = data_207 ∧ Good (rowAt 207) ∧ EntryGood 207) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group01_piece01_correct.2.2.2.1, trivial⟩
