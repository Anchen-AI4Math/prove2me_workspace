import Solutions.SnakyMilestones.Certificate35Block07Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block07_group01_correct : (rowAt 232 = data_232 ∧ Good (rowAt 232) ∧ EntryGood 232) ∧ (rowAt 233 = data_233 ∧ Good (rowAt 233) ∧ EntryGood 233) ∧ (rowAt 234 = data_234 ∧ Good (rowAt 234) ∧ EntryGood 234) ∧ (rowAt 235 = data_235 ∧ Good (rowAt 235) ∧ EntryGood 235) ∧ (rowAt 236 = data_236 ∧ Good (rowAt 236) ∧ EntryGood 236) ∧ (rowAt 237 = data_237 ∧ Good (rowAt 237) ∧ EntryGood 237) ∧ (rowAt 238 = data_238 ∧ Good (rowAt 238) ∧ EntryGood 238) ∧ (rowAt 239 = data_239 ∧ Good (rowAt 239) ∧ EntryGood 239) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
