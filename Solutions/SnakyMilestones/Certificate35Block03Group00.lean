import Solutions.SnakyMilestones.Certificate35Block03Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block03_group00_correct : (rowAt 96 = data_96 ∧ Good (rowAt 96) ∧ EntryGood 96) ∧ (rowAt 97 = data_97 ∧ Good (rowAt 97) ∧ EntryGood 97) ∧ (rowAt 98 = data_98 ∧ Good (rowAt 98) ∧ EntryGood 98) ∧ (rowAt 99 = data_99 ∧ Good (rowAt 99) ∧ EntryGood 99) ∧ (rowAt 100 = data_100 ∧ Good (rowAt 100) ∧ EntryGood 100) ∧ (rowAt 101 = data_101 ∧ Good (rowAt 101) ∧ EntryGood 101) ∧ (rowAt 102 = data_102 ∧ Good (rowAt 102) ∧ EntryGood 102) ∧ (rowAt 103 = data_103 ∧ Good (rowAt 103) ∧ EntryGood 103) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group00_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
