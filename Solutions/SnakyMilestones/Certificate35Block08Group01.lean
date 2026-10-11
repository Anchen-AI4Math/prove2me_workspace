import Solutions.SnakyMilestones.Certificate35Block08Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block08_group01_correct : (rowAt 264 = data_264 ∧ Good (rowAt 264) ∧ EntryGood 264) ∧ (rowAt 265 = data_265 ∧ Good (rowAt 265) ∧ EntryGood 265) ∧ (rowAt 266 = data_266 ∧ Good (rowAt 266) ∧ EntryGood 266) ∧ (rowAt 267 = data_267 ∧ Good (rowAt 267) ∧ EntryGood 267) ∧ (rowAt 268 = data_268 ∧ Good (rowAt 268) ∧ EntryGood 268) ∧ (rowAt 269 = data_269 ∧ Good (rowAt 269) ∧ EntryGood 269) ∧ (rowAt 270 = data_270 ∧ Good (rowAt 270) ∧ EntryGood 270) ∧ (rowAt 271 = data_271 ∧ Good (rowAt 271) ∧ EntryGood 271) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
