import Solutions.SnakyMilestones.Certificate35Block07Group03Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block07_group03_correct : (rowAt 248 = data_248 ∧ Good (rowAt 248) ∧ EntryGood 248) ∧ (rowAt 249 = data_249 ∧ Good (rowAt 249) ∧ EntryGood 249) ∧ (rowAt 250 = data_250 ∧ Good (rowAt 250) ∧ EntryGood 250) ∧ (rowAt 251 = data_251 ∧ Good (rowAt 251) ∧ EntryGood 251) ∧ (rowAt 252 = data_252 ∧ Good (rowAt 252) ∧ EntryGood 252) ∧ (rowAt 253 = data_253 ∧ Good (rowAt 253) ∧ EntryGood 253) ∧ (rowAt 254 = data_254 ∧ Good (rowAt 254) ∧ EntryGood 254) ∧ (rowAt 255 = data_255 ∧ Good (rowAt 255) ∧ EntryGood 255) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group03_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
