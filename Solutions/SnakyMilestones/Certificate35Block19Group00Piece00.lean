import Definitions.Def_Snaky35Cache19
import Solutions.SnakyMilestones.Certificate35Part18
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_589_checked : entryAt 589 = entry_589 := by
  rw [entry_chunk_29 3 (by decide)]
  decide +kernel
theorem row_589 : rowAt 589 = data_589 := by
  rw [rowAt, dif_neg (by decide : ¬ 589 < 6), entry_589_checked]
  change forkRow [placeRow ⟨4, 1, 4, 3⟩ (rowAt 4), placeRow ⟨588, 0, 4, 5⟩ (rowAt 588)] = data_589
  rw [row_4, row_588]
  apply row_ext <;> decide +kernel
theorem entry_good_589 : EntryGood 589 := by
  unfold EntryGood
  rw [entry_589_checked]
  decide +kernel
theorem good_589 : Good (rowAt 589) := by
  rw [row_589]
  unfold Good
  decide +kernel

theorem entry_590_checked : entryAt 590 = entry_590 := by
  rw [entry_chunk_29 4 (by decide)]
  decide +kernel
theorem row_590 : rowAt 590 = data_590 := by
  rw [rowAt, dif_neg (by decide : ¬ 590 < 6), entry_590_checked]
  change forkRow [placeRow ⟨295, 7, 4, 3⟩ (rowAt 295), placeRow ⟨173, 7, 4, 3⟩ (rowAt 173), placeRow ⟨577, 0, 4, 7⟩ (rowAt 577), placeRow ⟨490, 0, 4, 7⟩ (rowAt 490), placeRow ⟨217, 5, 4, 3⟩ (rowAt 217)] = data_590
  rw [row_295, row_173, row_577, row_490, row_217]
  apply row_ext <;> decide +kernel
theorem entry_good_590 : EntryGood 590 := by
  unfold EntryGood
  rw [entry_590_checked]
  decide +kernel
theorem good_590 : Good (rowAt 590) := by
  rw [row_590]
  unfold Good
  decide +kernel

theorem entry_591_checked : entryAt 591 = entry_591 := by
  rw [entry_chunk_29 5 (by decide)]
  decide +kernel
theorem row_591 : rowAt 591 = data_591 := by
  rw [rowAt, dif_neg (by decide : ¬ 591 < 6), entry_591_checked]
  change forkRow [placeRow ⟨524, 0, 4, 5⟩ (rowAt 524), placeRow ⟨529, 1, 4, 1⟩ (rowAt 529), placeRow ⟨529, 3, 4, 1⟩ (rowAt 529), placeRow ⟨538, 1, 4, 1⟩ (rowAt 538), placeRow ⟨538, 3, 4, 1⟩ (rowAt 538), placeRow ⟨197, 5, 4, 1⟩ (rowAt 197)] = data_591
  rw [row_524, row_529, row_538, row_197]
  apply row_ext <;> decide +kernel
theorem entry_good_591 : EntryGood 591 := by
  unfold EntryGood
  rw [entry_591_checked]
  decide +kernel
theorem good_591 : Good (rowAt 591) := by
  rw [row_591]
  unfold Good
  decide +kernel

theorem entry_592_checked : entryAt 592 = entry_592 := by
  rw [entry_chunk_29 6 (by decide)]
  decide +kernel
theorem row_592 : rowAt 592 = data_592 := by
  rw [rowAt, dif_neg (by decide : ¬ 592 < 6), entry_592_checked]
  change forkRow [placeRow ⟨588, 0, 4, 5⟩ (rowAt 588), placeRow ⟨108, 7, 3, 0⟩ (rowAt 108)] = data_592
  rw [row_588, row_108]
  apply row_ext <;> decide +kernel
theorem entry_good_592 : EntryGood 592 := by
  unfold EntryGood
  rw [entry_592_checked]
  decide +kernel
theorem good_592 : Good (rowAt 592) := by
  rw [row_592]
  unfold Good
  decide +kernel


theorem block19_group00_piece00_correct : (rowAt 589 = data_589 ∧ Good (rowAt 589) ∧ EntryGood 589) ∧ (rowAt 590 = data_590 ∧ Good (rowAt 590) ∧ EntryGood 590) ∧ (rowAt 591 = data_591 ∧ Good (rowAt 591) ∧ EntryGood 591) ∧ (rowAt 592 = data_592 ∧ Good (rowAt 592) ∧ EntryGood 592) ∧ True := by
  exact ⟨⟨row_589, good_589, entry_good_589⟩, ⟨row_590, good_590, entry_good_590⟩, ⟨row_591, good_591, entry_good_591⟩, ⟨row_592, good_592, entry_good_592⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
