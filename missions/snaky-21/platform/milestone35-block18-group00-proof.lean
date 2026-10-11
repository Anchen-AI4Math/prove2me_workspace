import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group00_piece00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block18_group00_piece01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 571 = data_571 ∧ Good (rowAt 571) ∧ EntryGood 571) ∧ (rowAt 572 = data_572 ∧ Good (rowAt 572) ∧ EntryGood 572) ∧ (rowAt 573 = data_573 ∧ Good (rowAt 573) ∧ EntryGood 573) ∧ (rowAt 574 = data_574 ∧ Good (rowAt 574) ∧ EntryGood 574) ∧ (rowAt 575 = data_575 ∧ Good (rowAt 575) ∧ EntryGood 575) ∧ (rowAt 576 = data_576 ∧ Good (rowAt 576) ∧ EntryGood 576) ∧ (rowAt 577 = data_577 ∧ Good (rowAt 577) ∧ EntryGood 577) ∧ (rowAt 578 = data_578 ∧ Good (rowAt 578) ∧ EntryGood 578) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece01_correct.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece01_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece01_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block18_group00_piece01_correct.2.2.2.1, trivial⟩
