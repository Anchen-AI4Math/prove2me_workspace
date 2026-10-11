import Solutions.SnakyMilestones.Certificate35Block16Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block16_group03_correct : (rowAt 536 = data_536 ∧ Good (rowAt 536) ∧ EntryGood 536) ∧ (rowAt 537 = data_537 ∧ Good (rowAt 537) ∧ EntryGood 537) ∧ (rowAt 538 = data_538 ∧ Good (rowAt 538) ∧ EntryGood 538) ∧ (rowAt 539 = data_539 ∧ Good (rowAt 539) ∧ EntryGood 539) ∧ (rowAt 540 = data_540 ∧ Good (rowAt 540) ∧ EntryGood 540) ∧ (rowAt 541 = data_541 ∧ Good (rowAt 541) ∧ EntryGood 541) ∧ (rowAt 542 = data_542 ∧ Good (rowAt 542) ∧ EntryGood 542) ∧ (rowAt 543 = data_543 ∧ Good (rowAt 543) ∧ EntryGood 543) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
