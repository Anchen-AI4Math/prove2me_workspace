import Solutions.SnakyMilestones.Certificate35Block19Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem block19_correct : (rowAt 589 = data_589 ∧ Good (rowAt 589) ∧ EntryGood 589) ∧ (rowAt 590 = data_590 ∧ Good (rowAt 590) ∧ EntryGood 590) ∧ (rowAt 591 = data_591 ∧ Good (rowAt 591) ∧ EntryGood 591) ∧ (rowAt 592 = data_592 ∧ Good (rowAt 592) ∧ EntryGood 592) ∧ (rowAt 593 = data_593 ∧ Good (rowAt 593) ∧ EntryGood 593) ∧ (rowAt 594 = data_594 ∧ Good (rowAt 594) ∧ EntryGood 594) ∧ (rowAt 595 = data_595 ∧ Good (rowAt 595) ∧ EntryGood 595) ∧ (rowAt 596 = data_596 ∧ Good (rowAt 596) ∧ EntryGood 596) ∧ (rowAt 597 = data_597 ∧ Good (rowAt 597) ∧ EntryGood 597) ∧ (rowAt 598 = data_598 ∧ Good (rowAt 598) ∧ EntryGood 598) ∧ (rowAt 599 = data_599 ∧ Good (rowAt 599) ∧ EntryGood 599) ∧ (rowAt 600 = data_600 ∧ Good (rowAt 600) ∧ EntryGood 600) ∧ True := by
  exact ⟨⟨row_589, good_589, entry_good_589⟩, ⟨row_590, good_590, entry_good_590⟩, ⟨row_591, good_591, entry_good_591⟩, ⟨row_592, good_592, entry_good_592⟩, ⟨row_593, good_593, entry_good_593⟩, ⟨row_594, good_594, entry_good_594⟩, ⟨row_595, good_595, entry_good_595⟩, ⟨row_596, good_596, entry_good_596⟩, ⟨row_597, good_597, entry_good_597⟩, ⟨row_598, good_598, entry_good_598⟩, ⟨row_599, good_599, entry_good_599⟩, ⟨row_600, good_600, entry_good_600⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
