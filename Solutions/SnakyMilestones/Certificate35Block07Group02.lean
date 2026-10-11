import Solutions.SnakyMilestones.Certificate35Block07Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block07_group02_correct : (rowAt 240 = data_240 ∧ Good (rowAt 240) ∧ EntryGood 240) ∧ (rowAt 241 = data_241 ∧ Good (rowAt 241) ∧ EntryGood 241) ∧ (rowAt 242 = data_242 ∧ Good (rowAt 242) ∧ EntryGood 242) ∧ (rowAt 243 = data_243 ∧ Good (rowAt 243) ∧ EntryGood 243) ∧ (rowAt 244 = data_244 ∧ Good (rowAt 244) ∧ EntryGood 244) ∧ (rowAt 245 = data_245 ∧ Good (rowAt 245) ∧ EntryGood 245) ∧ (rowAt 246 = data_246 ∧ Good (rowAt 246) ∧ EntryGood 246) ∧ (rowAt 247 = data_247 ∧ Good (rowAt 247) ∧ EntryGood 247) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block07_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
