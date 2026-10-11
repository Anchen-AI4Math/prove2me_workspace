import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block06_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 216 = data_216 ∧ Good (rowAt 216) ∧ EntryGood 216) ∧ (rowAt 217 = data_217 ∧ Good (rowAt 217) ∧ EntryGood 217) ∧ (rowAt 218 = data_218 ∧ Good (rowAt 218) ∧ EntryGood 218) ∧ (rowAt 219 = data_219 ∧ Good (rowAt 219) ∧ EntryGood 219) ∧ (rowAt 220 = data_220 ∧ Good (rowAt 220) ∧ EntryGood 220) ∧ (rowAt 221 = data_221 ∧ Good (rowAt 221) ∧ EntryGood 221) ∧ (rowAt 222 = data_222 ∧ Good (rowAt 222) ∧ EntryGood 222) ∧ (rowAt 223 = data_223 ∧ Good (rowAt 223) ∧ EntryGood 223) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block06_group03_piece01_correct.2.2.2.1, trivial⟩
