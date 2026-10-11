import Solutions.SnakyMilestones.Certificate35Block10Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block10_group01_correct : (rowAt 328 = data_328 ∧ Good (rowAt 328) ∧ EntryGood 328) ∧ (rowAt 329 = data_329 ∧ Good (rowAt 329) ∧ EntryGood 329) ∧ (rowAt 330 = data_330 ∧ Good (rowAt 330) ∧ EntryGood 330) ∧ (rowAt 331 = data_331 ∧ Good (rowAt 331) ∧ EntryGood 331) ∧ (rowAt 332 = data_332 ∧ Good (rowAt 332) ∧ EntryGood 332) ∧ (rowAt 333 = data_333 ∧ Good (rowAt 333) ∧ EntryGood 333) ∧ (rowAt 334 = data_334 ∧ Good (rowAt 334) ∧ EntryGood 334) ∧ (rowAt 335 = data_335 ∧ Good (rowAt 335) ∧ EntryGood 335) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
