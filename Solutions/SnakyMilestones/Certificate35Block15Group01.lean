import Solutions.SnakyMilestones.Certificate35Block15Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block15_group01_correct : (rowAt 488 = data_488 ∧ Good (rowAt 488) ∧ EntryGood 488) ∧ (rowAt 489 = data_489 ∧ Good (rowAt 489) ∧ EntryGood 489) ∧ (rowAt 490 = data_490 ∧ Good (rowAt 490) ∧ EntryGood 490) ∧ (rowAt 491 = data_491 ∧ Good (rowAt 491) ∧ EntryGood 491) ∧ (rowAt 492 = data_492 ∧ Good (rowAt 492) ∧ EntryGood 492) ∧ (rowAt 493 = data_493 ∧ Good (rowAt 493) ∧ EntryGood 493) ∧ (rowAt 494 = data_494 ∧ Good (rowAt 494) ∧ EntryGood 494) ∧ (rowAt 495 = data_495 ∧ Good (rowAt 495) ∧ EntryGood 495) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
