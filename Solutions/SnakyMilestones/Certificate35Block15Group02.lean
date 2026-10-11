import Solutions.SnakyMilestones.Certificate35Block15Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block15_group02_correct : (rowAt 496 = data_496 ∧ Good (rowAt 496) ∧ EntryGood 496) ∧ (rowAt 497 = data_497 ∧ Good (rowAt 497) ∧ EntryGood 497) ∧ (rowAt 498 = data_498 ∧ Good (rowAt 498) ∧ EntryGood 498) ∧ (rowAt 499 = data_499 ∧ Good (rowAt 499) ∧ EntryGood 499) ∧ (rowAt 500 = data_500 ∧ Good (rowAt 500) ∧ EntryGood 500) ∧ (rowAt 501 = data_501 ∧ Good (rowAt 501) ∧ EntryGood 501) ∧ (rowAt 502 = data_502 ∧ Good (rowAt 502) ∧ EntryGood 502) ∧ (rowAt 503 = data_503 ∧ Good (rowAt 503) ∧ EntryGood 503) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block15_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
