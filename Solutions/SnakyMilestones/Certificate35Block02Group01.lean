import Solutions.SnakyMilestones.Certificate35Block02Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block02_group01_correct : (rowAt 72 = data_72 ∧ Good (rowAt 72) ∧ EntryGood 72) ∧ (rowAt 73 = data_73 ∧ Good (rowAt 73) ∧ EntryGood 73) ∧ (rowAt 74 = data_74 ∧ Good (rowAt 74) ∧ EntryGood 74) ∧ (rowAt 75 = data_75 ∧ Good (rowAt 75) ∧ EntryGood 75) ∧ (rowAt 76 = data_76 ∧ Good (rowAt 76) ∧ EntryGood 76) ∧ (rowAt 77 = data_77 ∧ Good (rowAt 77) ∧ EntryGood 77) ∧ (rowAt 78 = data_78 ∧ Good (rowAt 78) ∧ EntryGood 78) ∧ (rowAt 79 = data_79 ∧ Good (rowAt 79) ∧ EntryGood 79) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block02_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
