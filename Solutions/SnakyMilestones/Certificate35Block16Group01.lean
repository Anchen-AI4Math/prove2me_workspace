import Solutions.SnakyMilestones.Certificate35Block16Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block16_group01_correct : (rowAt 520 = data_520 ∧ Good (rowAt 520) ∧ EntryGood 520) ∧ (rowAt 521 = data_521 ∧ Good (rowAt 521) ∧ EntryGood 521) ∧ (rowAt 522 = data_522 ∧ Good (rowAt 522) ∧ EntryGood 522) ∧ (rowAt 523 = data_523 ∧ Good (rowAt 523) ∧ EntryGood 523) ∧ (rowAt 524 = data_524 ∧ Good (rowAt 524) ∧ EntryGood 524) ∧ (rowAt 525 = data_525 ∧ Good (rowAt 525) ∧ EntryGood 525) ∧ (rowAt 526 = data_526 ∧ Good (rowAt 526) ∧ EntryGood 526) ∧ (rowAt 527 = data_527 ∧ Good (rowAt 527) ∧ EntryGood 527) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block16_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
