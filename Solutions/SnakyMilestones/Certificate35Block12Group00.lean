import Solutions.SnakyMilestones.Certificate35Block12Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block12_group00_correct : (rowAt 384 = data_384 ∧ Good (rowAt 384) ∧ EntryGood 384) ∧ (rowAt 385 = data_385 ∧ Good (rowAt 385) ∧ EntryGood 385) ∧ (rowAt 386 = data_386 ∧ Good (rowAt 386) ∧ EntryGood 386) ∧ (rowAt 387 = data_387 ∧ Good (rowAt 387) ∧ EntryGood 387) ∧ (rowAt 388 = data_388 ∧ Good (rowAt 388) ∧ EntryGood 388) ∧ (rowAt 389 = data_389 ∧ Good (rowAt 389) ∧ EntryGood 389) ∧ (rowAt 390 = data_390 ∧ Good (rowAt 390) ∧ EntryGood 390) ∧ (rowAt 391 = data_391 ∧ Good (rowAt 391) ∧ EntryGood 391) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block12_group00_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
