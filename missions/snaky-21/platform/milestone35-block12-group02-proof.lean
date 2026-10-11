import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group02_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block12_group02_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 400 = data_400 ∧ Good (rowAt 400) ∧ EntryGood 400) ∧ (rowAt 401 = data_401 ∧ Good (rowAt 401) ∧ EntryGood 401) ∧ (rowAt 402 = data_402 ∧ Good (rowAt 402) ∧ EntryGood 402) ∧ (rowAt 403 = data_403 ∧ Good (rowAt 403) ∧ EntryGood 403) ∧ (rowAt 404 = data_404 ∧ Good (rowAt 404) ∧ EntryGood 404) ∧ (rowAt 405 = data_405 ∧ Good (rowAt 405) ∧ EntryGood 405) ∧ (rowAt 406 = data_406 ∧ Good (rowAt 406) ∧ EntryGood 406) ∧ (rowAt 407 = data_407 ∧ Good (rowAt 407) ∧ EntryGood 407) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group02_piece01_correct.2.2.2.1, trivial⟩
