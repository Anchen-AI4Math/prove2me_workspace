import Solutions.SnakyMilestones.Certificate35Block09Group01Piece01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block09_group01_correct : (rowAt 296 = data_296 ∧ Good (rowAt 296) ∧ EntryGood 296) ∧ (rowAt 297 = data_297 ∧ Good (rowAt 297) ∧ EntryGood 297) ∧ (rowAt 298 = data_298 ∧ Good (rowAt 298) ∧ EntryGood 298) ∧ (rowAt 299 = data_299 ∧ Good (rowAt 299) ∧ EntryGood 299) ∧ (rowAt 300 = data_300 ∧ Good (rowAt 300) ∧ EntryGood 300) ∧ (rowAt 301 = data_301 ∧ Good (rowAt 301) ∧ EntryGood 301) ∧ (rowAt 302 = data_302 ∧ Good (rowAt 302) ∧ EntryGood 302) ∧ (rowAt 303 = data_303 ∧ Good (rowAt 303) ∧ EntryGood 303) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block09_group01_piece01_correct.2.2.2.1, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
