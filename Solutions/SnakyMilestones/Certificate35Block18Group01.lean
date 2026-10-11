import Solutions.SnakyMilestones.Certificate35Block18Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block18_group01_correct : (rowAt 579 = data_579 ∧ Good (rowAt 579) ∧ EntryGood 579) ∧ (rowAt 580 = data_580 ∧ Good (rowAt 580) ∧ EntryGood 580) ∧ (rowAt 581 = data_581 ∧ Good (rowAt 581) ∧ EntryGood 581) ∧ (rowAt 582 = data_582 ∧ Good (rowAt 582) ∧ EntryGood 582) ∧ (rowAt 583 = data_583 ∧ Good (rowAt 583) ∧ EntryGood 583) ∧ (rowAt 584 = data_584 ∧ Good (rowAt 584) ∧ EntryGood 584) ∧ (rowAt 585 = data_585 ∧ Good (rowAt 585) ∧ EntryGood 585) ∧ (rowAt 586 = data_586 ∧ Good (rowAt 586) ∧ EntryGood 586) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
