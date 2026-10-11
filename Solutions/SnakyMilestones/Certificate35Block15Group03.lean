import Solutions.SnakyMilestones.Certificate35Block15Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block15_group03_correct : (rowAt 504 = data_504 ∧ Good (rowAt 504) ∧ EntryGood 504) ∧ (rowAt 505 = data_505 ∧ Good (rowAt 505) ∧ EntryGood 505) ∧ (rowAt 506 = data_506 ∧ Good (rowAt 506) ∧ EntryGood 506) ∧ (rowAt 507 = data_507 ∧ Good (rowAt 507) ∧ EntryGood 507) ∧ (rowAt 508 = data_508 ∧ Good (rowAt 508) ∧ EntryGood 508) ∧ (rowAt 509 = data_509 ∧ Good (rowAt 509) ∧ EntryGood 509) ∧ (rowAt 510 = data_510 ∧ Good (rowAt 510) ∧ EntryGood 510) ∧ (rowAt 511 = data_511 ∧ Good (rowAt 511) ∧ EntryGood 511) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
