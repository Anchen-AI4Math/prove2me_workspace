import Solutions.SnakyMilestones.Certificate35Block14Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block14_group01_correct : (rowAt 456 = data_456 ∧ Good (rowAt 456) ∧ EntryGood 456) ∧ (rowAt 457 = data_457 ∧ Good (rowAt 457) ∧ EntryGood 457) ∧ (rowAt 458 = data_458 ∧ Good (rowAt 458) ∧ EntryGood 458) ∧ (rowAt 459 = data_459 ∧ Good (rowAt 459) ∧ EntryGood 459) ∧ (rowAt 460 = data_460 ∧ Good (rowAt 460) ∧ EntryGood 460) ∧ (rowAt 461 = data_461 ∧ Good (rowAt 461) ∧ EntryGood 461) ∧ (rowAt 462 = data_462 ∧ Good (rowAt 462) ∧ EntryGood 462) ∧ (rowAt 463 = data_463 ∧ Good (rowAt 463) ∧ EntryGood 463) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block14_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
