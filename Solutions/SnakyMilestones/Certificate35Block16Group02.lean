import Solutions.SnakyMilestones.Certificate35Block16Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block16_group02_correct : (rowAt 528 = data_528 ∧ Good (rowAt 528) ∧ EntryGood 528) ∧ (rowAt 529 = data_529 ∧ Good (rowAt 529) ∧ EntryGood 529) ∧ (rowAt 530 = data_530 ∧ Good (rowAt 530) ∧ EntryGood 530) ∧ (rowAt 531 = data_531 ∧ Good (rowAt 531) ∧ EntryGood 531) ∧ (rowAt 532 = data_532 ∧ Good (rowAt 532) ∧ EntryGood 532) ∧ (rowAt 533 = data_533 ∧ Good (rowAt 533) ∧ EntryGood 533) ∧ (rowAt 534 = data_534 ∧ Good (rowAt 534) ∧ EntryGood 534) ∧ (rowAt 535 = data_535 ∧ Good (rowAt 535) ∧ EntryGood 535) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
