import Solutions.SnakyMilestones.Certificate35Block08Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block08_group02_correct : (rowAt 272 = data_272 ∧ Good (rowAt 272) ∧ EntryGood 272) ∧ (rowAt 273 = data_273 ∧ Good (rowAt 273) ∧ EntryGood 273) ∧ (rowAt 274 = data_274 ∧ Good (rowAt 274) ∧ EntryGood 274) ∧ (rowAt 275 = data_275 ∧ Good (rowAt 275) ∧ EntryGood 275) ∧ (rowAt 276 = data_276 ∧ Good (rowAt 276) ∧ EntryGood 276) ∧ (rowAt 277 = data_277 ∧ Good (rowAt 277) ∧ EntryGood 277) ∧ (rowAt 278 = data_278 ∧ Good (rowAt 278) ∧ EntryGood 278) ∧ (rowAt 279 = data_279 ∧ Good (rowAt 279) ∧ EntryGood 279) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block08_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
