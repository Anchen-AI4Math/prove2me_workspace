import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block08_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 280 = data_280 ∧ Good (rowAt 280) ∧ EntryGood 280) ∧ (rowAt 281 = data_281 ∧ Good (rowAt 281) ∧ EntryGood 281) ∧ (rowAt 282 = data_282 ∧ Good (rowAt 282) ∧ EntryGood 282) ∧ (rowAt 283 = data_283 ∧ Good (rowAt 283) ∧ EntryGood 283) ∧ (rowAt 284 = data_284 ∧ Good (rowAt 284) ∧ EntryGood 284) ∧ (rowAt 285 = data_285 ∧ Good (rowAt 285) ∧ EntryGood 285) ∧ (rowAt 286 = data_286 ∧ Good (rowAt 286) ∧ EntryGood 286) ∧ (rowAt 287 = data_287 ∧ Good (rowAt 287) ∧ EntryGood 287) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group03_piece01_correct.2.2.2.1, trivial⟩
