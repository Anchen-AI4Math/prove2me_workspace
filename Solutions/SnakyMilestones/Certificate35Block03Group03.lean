import Solutions.SnakyMilestones.Certificate35Block03Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block03_group03_correct : (rowAt 120 = data_120 ∧ Good (rowAt 120) ∧ EntryGood 120) ∧ (rowAt 121 = data_121 ∧ Good (rowAt 121) ∧ EntryGood 121) ∧ (rowAt 122 = data_122 ∧ Good (rowAt 122) ∧ EntryGood 122) ∧ (rowAt 123 = data_123 ∧ Good (rowAt 123) ∧ EntryGood 123) ∧ (rowAt 124 = data_124 ∧ Good (rowAt 124) ∧ EntryGood 124) ∧ (rowAt 125 = data_125 ∧ Good (rowAt 125) ∧ EntryGood 125) ∧ (rowAt 126 = data_126 ∧ Good (rowAt 126) ∧ EntryGood 126) ∧ (rowAt 127 = data_127 ∧ Good (rowAt 127) ∧ EntryGood 127) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
