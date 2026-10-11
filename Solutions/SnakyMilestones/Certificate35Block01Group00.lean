import Solutions.SnakyMilestones.Certificate35Block01Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block01_group00_correct : (rowAt 32 = data_32 ∧ Good (rowAt 32) ∧ EntryGood 32) ∧ (rowAt 33 = data_33 ∧ Good (rowAt 33) ∧ EntryGood 33) ∧ (rowAt 34 = data_34 ∧ Good (rowAt 34) ∧ EntryGood 34) ∧ (rowAt 35 = data_35 ∧ Good (rowAt 35) ∧ EntryGood 35) ∧ (rowAt 36 = data_36 ∧ Good (rowAt 36) ∧ EntryGood 36) ∧ (rowAt 37 = data_37 ∧ Good (rowAt 37) ∧ EntryGood 37) ∧ (rowAt 38 = data_38 ∧ Good (rowAt 38) ∧ EntryGood 38) ∧ (rowAt 39 = data_39 ∧ Good (rowAt 39) ∧ EntryGood 39) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block01_group00_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
