import Solutions.SnakyMilestones.Certificate35Block13Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block13_group03_correct : (rowAt 440 = data_440 ∧ Good (rowAt 440) ∧ EntryGood 440) ∧ (rowAt 441 = data_441 ∧ Good (rowAt 441) ∧ EntryGood 441) ∧ (rowAt 442 = data_442 ∧ Good (rowAt 442) ∧ EntryGood 442) ∧ (rowAt 443 = data_443 ∧ Good (rowAt 443) ∧ EntryGood 443) ∧ (rowAt 444 = data_444 ∧ Good (rowAt 444) ∧ EntryGood 444) ∧ (rowAt 445 = data_445 ∧ Good (rowAt 445) ∧ EntryGood 445) ∧ (rowAt 446 = data_446 ∧ Good (rowAt 446) ∧ EntryGood 446) ∧ (rowAt 447 = data_447 ∧ Good (rowAt 447) ∧ EntryGood 447) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
