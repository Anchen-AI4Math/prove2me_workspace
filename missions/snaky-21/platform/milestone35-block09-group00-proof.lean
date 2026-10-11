import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block09_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 288 = data_288 ∧ Good (rowAt 288) ∧ EntryGood 288) ∧ (rowAt 289 = data_289 ∧ Good (rowAt 289) ∧ EntryGood 289) ∧ (rowAt 290 = data_290 ∧ Good (rowAt 290) ∧ EntryGood 290) ∧ (rowAt 291 = data_291 ∧ Good (rowAt 291) ∧ EntryGood 291) ∧ (rowAt 292 = data_292 ∧ Good (rowAt 292) ∧ EntryGood 292) ∧ (rowAt 293 = data_293 ∧ Good (rowAt 293) ∧ EntryGood 293) ∧ (rowAt 294 = data_294 ∧ Good (rowAt 294) ∧ EntryGood 294) ∧ (rowAt 295 = data_295 ∧ Good (rowAt 295) ∧ EntryGood 295) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group00_piece01_correct.2.2.2.1, trivial⟩
