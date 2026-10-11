import Solutions.SnakyMilestones.Certificate35Block20Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block20_correct : (rowAt 601 = data_601 ∧ Good (rowAt 601) ∧ EntryGood 601) ∧ (rowAt 602 = data_602 ∧ Good (rowAt 602) ∧ EntryGood 602) ∧ (rowAt 603 = data_603 ∧ Good (rowAt 603) ∧ EntryGood 603) ∧ (rowAt 604 = data_604 ∧ Good (rowAt 604) ∧ EntryGood 604) ∧ (rowAt 605 = data_605 ∧ Good (rowAt 605) ∧ EntryGood 605) ∧ (rowAt 606 = data_606 ∧ Good (rowAt 606) ∧ EntryGood 606) ∧ (rowAt 607 = data_607 ∧ Good (rowAt 607) ∧ EntryGood 607) ∧ (rowAt 608 = data_608 ∧ Good (rowAt 608) ∧ EntryGood 608) ∧ (rowAt 609 = data_609 ∧ Good (rowAt 609) ∧ EntryGood 609) ∧ True := by
  exact ⟨⟨row_601, good_601, entry_good_601⟩, ⟨row_602, good_602, entry_good_602⟩, ⟨row_603, good_603, entry_good_603⟩, ⟨row_604, good_604, entry_good_604⟩, ⟨row_605, good_605, entry_good_605⟩, ⟨row_606, good_606, entry_good_606⟩, ⟨row_607, good_607, entry_good_607⟩, ⟨row_608, good_608, entry_good_608⟩, ⟨row_609, good_609, entry_good_609⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
