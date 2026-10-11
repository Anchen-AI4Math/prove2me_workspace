import Solutions.SnakyMilestones.Certificate35Block11Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block11_group01_correct : (rowAt 360 = data_360 ∧ Good (rowAt 360) ∧ EntryGood 360) ∧ (rowAt 361 = data_361 ∧ Good (rowAt 361) ∧ EntryGood 361) ∧ (rowAt 362 = data_362 ∧ Good (rowAt 362) ∧ EntryGood 362) ∧ (rowAt 363 = data_363 ∧ Good (rowAt 363) ∧ EntryGood 363) ∧ (rowAt 364 = data_364 ∧ Good (rowAt 364) ∧ EntryGood 364) ∧ (rowAt 365 = data_365 ∧ Good (rowAt 365) ∧ EntryGood 365) ∧ (rowAt 366 = data_366 ∧ Good (rowAt 366) ∧ EntryGood 366) ∧ (rowAt 367 = data_367 ∧ Good (rowAt 367) ∧ EntryGood 367) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
