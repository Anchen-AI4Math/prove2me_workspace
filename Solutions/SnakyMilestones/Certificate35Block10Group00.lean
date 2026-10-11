import Solutions.SnakyMilestones.Certificate35Block10Group00Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block10_group00_correct : (rowAt 320 = data_320 ∧ Good (rowAt 320) ∧ EntryGood 320) ∧ (rowAt 321 = data_321 ∧ Good (rowAt 321) ∧ EntryGood 321) ∧ (rowAt 322 = data_322 ∧ Good (rowAt 322) ∧ EntryGood 322) ∧ (rowAt 323 = data_323 ∧ Good (rowAt 323) ∧ EntryGood 323) ∧ (rowAt 324 = data_324 ∧ Good (rowAt 324) ∧ EntryGood 324) ∧ (rowAt 325 = data_325 ∧ Good (rowAt 325) ∧ EntryGood 325) ∧ (rowAt 326 = data_326 ∧ Good (rowAt 326) ∧ EntryGood 326) ∧ (rowAt 327 = data_327 ∧ Good (rowAt 327) ∧ EntryGood 327) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block10_group00_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
