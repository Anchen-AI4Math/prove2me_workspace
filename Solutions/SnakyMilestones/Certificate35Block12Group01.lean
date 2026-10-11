import Solutions.SnakyMilestones.Certificate35Block12Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block12_group01_correct : (rowAt 392 = data_392 ∧ Good (rowAt 392) ∧ EntryGood 392) ∧ (rowAt 393 = data_393 ∧ Good (rowAt 393) ∧ EntryGood 393) ∧ (rowAt 394 = data_394 ∧ Good (rowAt 394) ∧ EntryGood 394) ∧ (rowAt 395 = data_395 ∧ Good (rowAt 395) ∧ EntryGood 395) ∧ (rowAt 396 = data_396 ∧ Good (rowAt 396) ∧ EntryGood 396) ∧ (rowAt 397 = data_397 ∧ Good (rowAt 397) ∧ EntryGood 397) ∧ (rowAt 398 = data_398 ∧ Good (rowAt 398) ∧ EntryGood 398) ∧ (rowAt 399 = data_399 ∧ Good (rowAt 399) ∧ EntryGood 399) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
