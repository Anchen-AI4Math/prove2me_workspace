import Solutions.SnakyMilestones.Certificate35Block21Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block21_group00_correct : (rowAt 610 = data_610 ∧ Good (rowAt 610) ∧ EntryGood 610) ∧ (rowAt 611 = data_611 ∧ Good (rowAt 611) ∧ EntryGood 611) ∧ (rowAt 612 = data_612 ∧ Good (rowAt 612) ∧ EntryGood 612) ∧ (rowAt 613 = data_613 ∧ Good (rowAt 613) ∧ EntryGood 613) ∧ (rowAt 614 = data_614 ∧ Good (rowAt 614) ∧ EntryGood 614) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block21_group00_piece01_correct.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
