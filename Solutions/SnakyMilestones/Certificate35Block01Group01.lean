import Solutions.SnakyMilestones.Certificate35Block01Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block01_group01_correct : (rowAt 40 = data_40 ∧ Good (rowAt 40) ∧ EntryGood 40) ∧ (rowAt 41 = data_41 ∧ Good (rowAt 41) ∧ EntryGood 41) ∧ (rowAt 42 = data_42 ∧ Good (rowAt 42) ∧ EntryGood 42) ∧ (rowAt 43 = data_43 ∧ Good (rowAt 43) ∧ EntryGood 43) ∧ (rowAt 44 = data_44 ∧ Good (rowAt 44) ∧ EntryGood 44) ∧ (rowAt 45 = data_45 ∧ Good (rowAt 45) ∧ EntryGood 45) ∧ (rowAt 46 = data_46 ∧ Good (rowAt 46) ∧ EntryGood 46) ∧ (rowAt 47 = data_47 ∧ Good (rowAt 47) ∧ EntryGood 47) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
