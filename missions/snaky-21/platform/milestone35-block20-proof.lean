import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block20_group00_correct
import Theorems.Thm_OAI_SnakyCertificate_MilestoneChecks_block20_group01_correct
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
open OAI.SnakyCertificate.MilestoneChecks OAI.SnakyCertificate
theorem solution : (rowAt 601 = data_601 ∧ Good (rowAt 601) ∧ EntryGood 601) ∧ (rowAt 602 = data_602 ∧ Good (rowAt 602) ∧ EntryGood 602) ∧ (rowAt 603 = data_603 ∧ Good (rowAt 603) ∧ EntryGood 603) ∧ (rowAt 604 = data_604 ∧ Good (rowAt 604) ∧ EntryGood 604) ∧ (rowAt 605 = data_605 ∧ Good (rowAt 605) ∧ EntryGood 605) ∧ (rowAt 606 = data_606 ∧ Good (rowAt 606) ∧ EntryGood 606) ∧ (rowAt 607 = data_607 ∧ Good (rowAt 607) ∧ EntryGood 607) ∧ (rowAt 608 = data_608 ∧ Good (rowAt 608) ∧ EntryGood 608) ∧ (rowAt 609 = data_609 ∧ Good (rowAt 609) ∧ EntryGood 609) ∧ True := by
  exact ⟨OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group00_correct.2.2.2.2.2.2.2.1, OAI.SnakyCertificate.MilestoneChecks.block20_group01_correct.1, trivial⟩
