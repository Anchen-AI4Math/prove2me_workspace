import Solutions.SnakyMilestones.Certificate35Block11Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block11_group03_correct : (rowAt 376 = data_376 ∧ Good (rowAt 376) ∧ EntryGood 376) ∧ (rowAt 377 = data_377 ∧ Good (rowAt 377) ∧ EntryGood 377) ∧ (rowAt 378 = data_378 ∧ Good (rowAt 378) ∧ EntryGood 378) ∧ (rowAt 379 = data_379 ∧ Good (rowAt 379) ∧ EntryGood 379) ∧ (rowAt 380 = data_380 ∧ Good (rowAt 380) ∧ EntryGood 380) ∧ (rowAt 381 = data_381 ∧ Good (rowAt 381) ∧ EntryGood 381) ∧ (rowAt 382 = data_382 ∧ Good (rowAt 382) ∧ EntryGood 382) ∧ (rowAt 383 = data_383 ∧ Good (rowAt 383) ∧ EntryGood 383) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block11_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
