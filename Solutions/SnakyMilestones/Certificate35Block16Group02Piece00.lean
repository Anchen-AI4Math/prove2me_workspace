import Definitions.Def_Snaky35Cache16
import Solutions.SnakyMilestones.Certificate35Block16Group01
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_528_checked : entryAt 528 = entry_528 := by
  rw [entry_chunk_26 2 (by decide)]
  decide +kernel
theorem row_528 : rowAt 528 = data_528 := by
  rw [rowAt, dif_neg (by decide : ¬ 528 < 6), entry_528_checked]
  change forkRow [placeRow ⟨414, 1, 3, 5⟩ (rowAt 414), placeRow ⟨386, 1, 4, 6⟩ (rowAt 386), placeRow ⟨502, 5, 4, 3⟩ (rowAt 502), placeRow ⟨226, 4, 1, 5⟩ (rowAt 226), placeRow ⟨359, 5, 3, 4⟩ (rowAt 359)] = data_528
  rw [row_414, row_386, row_502, row_226, row_359]
  apply row_ext <;> decide +kernel
theorem entry_good_528 : EntryGood 528 := by
  unfold EntryGood
  rw [entry_528_checked]
  decide +kernel
theorem good_528 : Good (rowAt 528) := by
  rw [row_528]
  unfold Good
  decide +kernel

theorem entry_529_checked : entryAt 529 = entry_529 := by
  rw [entry_chunk_26 3 (by decide)]
  decide +kernel
theorem row_529 : rowAt 529 = data_529 := by
  rw [rowAt, dif_neg (by decide : ¬ 529 < 6), entry_529_checked]
  change forkRow [placeRow ⟨55, 4, 3, 4⟩ (rowAt 55), placeRow ⟨441, 0, 4, 3⟩ (rowAt 441), placeRow ⟨63, 3, 3, 3⟩ (rowAt 63), placeRow ⟨64, 6, 7, 5⟩ (rowAt 64)] = data_529
  rw [row_55, row_441, row_63, row_64]
  apply row_ext <;> decide +kernel
theorem entry_good_529 : EntryGood 529 := by
  unfold EntryGood
  rw [entry_529_checked]
  decide +kernel
theorem good_529 : Good (rowAt 529) := by
  rw [row_529]
  unfold Good
  decide +kernel

theorem entry_530_checked : entryAt 530 = entry_530 := by
  rw [entry_chunk_26 4 (by decide)]
  decide +kernel
theorem row_530 : rowAt 530 = data_530 := by
  rw [rowAt, dif_neg (by decide : ¬ 530 < 6), entry_530_checked]
  change forkRow [placeRow ⟨456, 7, 4, 2⟩ (rowAt 456), placeRow ⟨336, 0, 5, 5⟩ (rowAt 336), placeRow ⟨283, 7, 4, 2⟩ (rowAt 283), placeRow ⟨271, 5, 5, 5⟩ (rowAt 271)] = data_530
  rw [row_456, row_336, row_283, row_271]
  apply row_ext <;> decide +kernel
theorem entry_good_530 : EntryGood 530 := by
  unfold EntryGood
  rw [entry_530_checked]
  decide +kernel
theorem good_530 : Good (rowAt 530) := by
  rw [row_530]
  unfold Good
  decide +kernel

theorem entry_531_checked : entryAt 531 = entry_531 := by
  rw [entry_chunk_26 5 (by decide)]
  decide +kernel
theorem row_531 : rowAt 531 = data_531 := by
  rw [rowAt, dif_neg (by decide : ¬ 531 < 6), entry_531_checked]
  change forkRow [placeRow ⟨425, 0, 5, 4⟩ (rowAt 425), placeRow ⟨336, 3, 4, 3⟩ (rowAt 336), placeRow ⟨340, 6, 4, 3⟩ (rowAt 340), placeRow ⟨394, 1, 5, 4⟩ (rowAt 394), placeRow ⟨423, 0, 5, 4⟩ (rowAt 423), placeRow ⟨526, 0, 5, 4⟩ (rowAt 526), placeRow ⟨401, 4, 4, 3⟩ (rowAt 401), placeRow ⟨453, 0, 5, 4⟩ (rowAt 453)] = data_531
  rw [row_425, row_336, row_340, row_394, row_423, row_526, row_401, row_453]
  apply row_ext <;> decide +kernel
theorem entry_good_531 : EntryGood 531 := by
  unfold EntryGood
  rw [entry_531_checked]
  decide +kernel
theorem good_531 : Good (rowAt 531) := by
  rw [row_531]
  unfold Good
  decide +kernel


theorem block16_group02_piece00_correct : (rowAt 528 = data_528 ∧ Good (rowAt 528) ∧ EntryGood 528) ∧ (rowAt 529 = data_529 ∧ Good (rowAt 529) ∧ EntryGood 529) ∧ (rowAt 530 = data_530 ∧ Good (rowAt 530) ∧ EntryGood 530) ∧ (rowAt 531 = data_531 ∧ Good (rowAt 531) ∧ EntryGood 531) ∧ True := by
  exact ⟨⟨row_528, good_528, entry_good_528⟩, ⟨row_529, good_529, entry_good_529⟩, ⟨row_530, good_530, entry_good_530⟩, ⟨row_531, good_531, entry_good_531⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
