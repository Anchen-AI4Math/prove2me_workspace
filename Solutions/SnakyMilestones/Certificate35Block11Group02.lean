import Solutions.SnakyMilestones.Certificate35Block11Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block11_group02_correct : (rowAt 368 = data_368 ∧ Good (rowAt 368) ∧ EntryGood 368) ∧ (rowAt 369 = data_369 ∧ Good (rowAt 369) ∧ EntryGood 369) ∧ (rowAt 370 = data_370 ∧ Good (rowAt 370) ∧ EntryGood 370) ∧ (rowAt 371 = data_371 ∧ Good (rowAt 371) ∧ EntryGood 371) ∧ (rowAt 372 = data_372 ∧ Good (rowAt 372) ∧ EntryGood 372) ∧ (rowAt 373 = data_373 ∧ Good (rowAt 373) ∧ EntryGood 373) ∧ (rowAt 374 = data_374 ∧ Good (rowAt 374) ∧ EntryGood 374) ∧ (rowAt 375 = data_375 ∧ Good (rowAt 375) ∧ EntryGood 375) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
