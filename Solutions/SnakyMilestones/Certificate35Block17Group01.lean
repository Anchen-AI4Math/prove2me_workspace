import Solutions.SnakyMilestones.Certificate35Block17Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block17_group01_correct : (rowAt 552 = data_552 ∧ Good (rowAt 552) ∧ EntryGood 552) ∧ (rowAt 553 = data_553 ∧ Good (rowAt 553) ∧ EntryGood 553) ∧ (rowAt 554 = data_554 ∧ Good (rowAt 554) ∧ EntryGood 554) ∧ (rowAt 555 = data_555 ∧ Good (rowAt 555) ∧ EntryGood 555) ∧ (rowAt 556 = data_556 ∧ Good (rowAt 556) ∧ EntryGood 556) ∧ (rowAt 557 = data_557 ∧ Good (rowAt 557) ∧ EntryGood 557) ∧ (rowAt 558 = data_558 ∧ Good (rowAt 558) ∧ EntryGood 558) ∧ (rowAt 559 = data_559 ∧ Good (rowAt 559) ∧ EntryGood 559) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
