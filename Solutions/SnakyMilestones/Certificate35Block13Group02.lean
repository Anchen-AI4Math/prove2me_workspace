import Solutions.SnakyMilestones.Certificate35Block13Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block13_group02_correct : (rowAt 432 = data_432 ∧ Good (rowAt 432) ∧ EntryGood 432) ∧ (rowAt 433 = data_433 ∧ Good (rowAt 433) ∧ EntryGood 433) ∧ (rowAt 434 = data_434 ∧ Good (rowAt 434) ∧ EntryGood 434) ∧ (rowAt 435 = data_435 ∧ Good (rowAt 435) ∧ EntryGood 435) ∧ (rowAt 436 = data_436 ∧ Good (rowAt 436) ∧ EntryGood 436) ∧ (rowAt 437 = data_437 ∧ Good (rowAt 437) ∧ EntryGood 437) ∧ (rowAt 438 = data_438 ∧ Good (rowAt 438) ∧ EntryGood 438) ∧ (rowAt 439 = data_439 ∧ Good (rowAt 439) ∧ EntryGood 439) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block13_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
