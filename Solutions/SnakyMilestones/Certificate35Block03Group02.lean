import Solutions.SnakyMilestones.Certificate35Block03Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block03_group02_correct : (rowAt 112 = data_112 ∧ Good (rowAt 112) ∧ EntryGood 112) ∧ (rowAt 113 = data_113 ∧ Good (rowAt 113) ∧ EntryGood 113) ∧ (rowAt 114 = data_114 ∧ Good (rowAt 114) ∧ EntryGood 114) ∧ (rowAt 115 = data_115 ∧ Good (rowAt 115) ∧ EntryGood 115) ∧ (rowAt 116 = data_116 ∧ Good (rowAt 116) ∧ EntryGood 116) ∧ (rowAt 117 = data_117 ∧ Good (rowAt 117) ∧ EntryGood 117) ∧ (rowAt 118 = data_118 ∧ Good (rowAt 118) ∧ EntryGood 118) ∧ (rowAt 119 = data_119 ∧ Good (rowAt 119) ∧ EntryGood 119) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block03_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
