import Solutions.SnakyMilestones.Certificate35Block00Group03Piece03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block00_group03_correct : (rowAt 24 = data_24 ∧ Good (rowAt 24) ∧ EntryGood 24) ∧ (rowAt 25 = data_25 ∧ Good (rowAt 25) ∧ EntryGood 25) ∧ (rowAt 26 = data_26 ∧ Good (rowAt 26) ∧ EntryGood 26) ∧ (rowAt 27 = data_27 ∧ Good (rowAt 27) ∧ EntryGood 27) ∧ (rowAt 28 = data_28 ∧ Good (rowAt 28) ∧ EntryGood 28) ∧ (rowAt 29 = data_29 ∧ Good (rowAt 29) ∧ EntryGood 29) ∧ (rowAt 30 = data_30 ∧ Good (rowAt 30) ∧ EntryGood 30) ∧ (rowAt 31 = data_31 ∧ Good (rowAt 31) ∧ EntryGood 31) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece02_correct.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece02_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece03_correct.1, OAI.SnakyCertificate.MilestoneChecks.block00_group03_piece03_correct.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
