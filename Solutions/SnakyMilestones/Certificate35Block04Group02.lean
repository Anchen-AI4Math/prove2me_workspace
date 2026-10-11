import Solutions.SnakyMilestones.Certificate35Block04Group02Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block04_group02_correct : (rowAt 144 = data_144 ∧ Good (rowAt 144) ∧ EntryGood 144) ∧ (rowAt 145 = data_145 ∧ Good (rowAt 145) ∧ EntryGood 145) ∧ (rowAt 146 = data_146 ∧ Good (rowAt 146) ∧ EntryGood 146) ∧ (rowAt 147 = data_147 ∧ Good (rowAt 147) ∧ EntryGood 147) ∧ (rowAt 148 = data_148 ∧ Good (rowAt 148) ∧ EntryGood 148) ∧ (rowAt 149 = data_149 ∧ Good (rowAt 149) ∧ EntryGood 149) ∧ (rowAt 150 = data_150 ∧ Good (rowAt 150) ∧ EntryGood 150) ∧ (rowAt 151 = data_151 ∧ Good (rowAt 151) ∧ EntryGood 151) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block04_group02_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
