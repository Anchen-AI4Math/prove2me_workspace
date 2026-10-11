import Solutions.SnakyMilestones.Certificate35Block17Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block17_group00_correct : (rowAt 544 = data_544 ∧ Good (rowAt 544) ∧ EntryGood 544) ∧ (rowAt 545 = data_545 ∧ Good (rowAt 545) ∧ EntryGood 545) ∧ (rowAt 546 = data_546 ∧ Good (rowAt 546) ∧ EntryGood 546) ∧ (rowAt 547 = data_547 ∧ Good (rowAt 547) ∧ EntryGood 547) ∧ (rowAt 548 = data_548 ∧ Good (rowAt 548) ∧ EntryGood 548) ∧ (rowAt 549 = data_549 ∧ Good (rowAt 549) ∧ EntryGood 549) ∧ (rowAt 550 = data_550 ∧ Good (rowAt 550) ∧ EntryGood 550) ∧ (rowAt 551 = data_551 ∧ Good (rowAt 551) ∧ EntryGood 551) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group00_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
