import Solutions.SnakyMilestones.Certificate35Block17Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block17_group02_correct : (rowAt 560 = data_560 ∧ Good (rowAt 560) ∧ EntryGood 560) ∧ (rowAt 561 = data_561 ∧ Good (rowAt 561) ∧ EntryGood 561) ∧ (rowAt 562 = data_562 ∧ Good (rowAt 562) ∧ EntryGood 562) ∧ (rowAt 563 = data_563 ∧ Good (rowAt 563) ∧ EntryGood 563) ∧ (rowAt 564 = data_564 ∧ Good (rowAt 564) ∧ EntryGood 564) ∧ (rowAt 565 = data_565 ∧ Good (rowAt 565) ∧ EntryGood 565) ∧ (rowAt 566 = data_566 ∧ Good (rowAt 566) ∧ EntryGood 566) ∧ (rowAt 567 = data_567 ∧ Good (rowAt 567) ∧ EntryGood 567) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block17_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
