import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group03_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block05_group03_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 184 = data_184 ∧ Good (rowAt 184) ∧ EntryGood 184) ∧ (rowAt 185 = data_185 ∧ Good (rowAt 185) ∧ EntryGood 185) ∧ (rowAt 186 = data_186 ∧ Good (rowAt 186) ∧ EntryGood 186) ∧ (rowAt 187 = data_187 ∧ Good (rowAt 187) ∧ EntryGood 187) ∧ (rowAt 188 = data_188 ∧ Good (rowAt 188) ∧ EntryGood 188) ∧ (rowAt 189 = data_189 ∧ Good (rowAt 189) ∧ EntryGood 189) ∧ (rowAt 190 = data_190 ∧ Good (rowAt 190) ∧ EntryGood 190) ∧ (rowAt 191 = data_191 ∧ Good (rowAt 191) ∧ EntryGood 191) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block05_group03_piece01_correct.2.2.2.1, trivial⟩
