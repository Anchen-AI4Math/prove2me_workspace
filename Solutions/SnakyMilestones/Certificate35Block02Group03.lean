import Solutions.SnakyMilestones.Certificate35Block02Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block02_group03_correct : (rowAt 88 = data_88 ∧ Good (rowAt 88) ∧ EntryGood 88) ∧ (rowAt 89 = data_89 ∧ Good (rowAt 89) ∧ EntryGood 89) ∧ (rowAt 90 = data_90 ∧ Good (rowAt 90) ∧ EntryGood 90) ∧ (rowAt 91 = data_91 ∧ Good (rowAt 91) ∧ EntryGood 91) ∧ (rowAt 92 = data_92 ∧ Good (rowAt 92) ∧ EntryGood 92) ∧ (rowAt 93 = data_93 ∧ Good (rowAt 93) ∧ EntryGood 93) ∧ (rowAt 94 = data_94 ∧ Good (rowAt 94) ∧ EntryGood 94) ∧ (rowAt 95 = data_95 ∧ Good (rowAt 95) ∧ EntryGood 95) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
