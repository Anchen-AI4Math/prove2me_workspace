import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 304 = data_304 ∧ Good (rowAt 304) ∧ EntryGood 304) ∧ (rowAt 305 = data_305 ∧ Good (rowAt 305) ∧ EntryGood 305) ∧ (rowAt 306 = data_306 ∧ Good (rowAt 306) ∧ EntryGood 306) ∧ (rowAt 307 = data_307 ∧ Good (rowAt 307) ∧ EntryGood 307) ∧ (rowAt 308 = data_308 ∧ Good (rowAt 308) ∧ EntryGood 308) ∧ (rowAt 309 = data_309 ∧ Good (rowAt 309) ∧ EntryGood 309) ∧ (rowAt 310 = data_310 ∧ Good (rowAt 310) ∧ EntryGood 310) ∧ (rowAt 311 = data_311 ∧ Good (rowAt 311) ∧ EntryGood 311) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group02_piece01_correct.2.2.2.1, trivial⟩
