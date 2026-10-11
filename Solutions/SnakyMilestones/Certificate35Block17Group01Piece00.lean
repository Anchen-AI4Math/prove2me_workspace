import Definitions.Def_Snaky35Cache17
import Solutions.SnakyMilestones.Certificate35Block17Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_552_checked : entryAt 552 = entry_552 := by
  rw [entry_chunk_27 6 (by decide)]
  decide +kernel
theorem row_552 : rowAt 552 = data_552 := by
  rw [rowAt, dif_neg (by decide : ¬ 552 < 6), entry_552_checked]
  change forkRow [placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨64, 2, 1, 5⟩ (rowAt 64), placeRow ⟨504, 1, 3, 3⟩ (rowAt 504), placeRow ⟨404, 5, 2, 3⟩ (rowAt 404)] = data_552
  rw [row_443, row_64, row_504, row_404]
  apply row_ext <;> decide +kernel
theorem entry_good_552 : EntryGood 552 := by
  unfold EntryGood
  rw [entry_552_checked]
  decide +kernel
theorem good_552 : Good (rowAt 552) := by
  rw [row_552]
  unfold Good
  decide +kernel

theorem entry_553_checked : entryAt 553 = entry_553 := by
  rw [entry_chunk_27 7 (by decide)]
  decide +kernel
theorem row_553 : rowAt 553 = data_553 := by
  rw [rowAt, dif_neg (by decide : ¬ 553 < 6), entry_553_checked]
  change forkRow [placeRow ⟨63, 0, 3, 5⟩ (rowAt 63), placeRow ⟨261, 4, 5, 4⟩ (rowAt 261), placeRow ⟨471, 0, 5, 1⟩ (rowAt 471), placeRow ⟨442, 0, 4, 5⟩ (rowAt 442), placeRow ⟨504, 0, 3, 3⟩ (rowAt 504), placeRow ⟨180, 0, 4, 5⟩ (rowAt 180)] = data_553
  rw [row_63, row_261, row_471, row_442, row_504, row_180]
  apply row_ext <;> decide +kernel
theorem entry_good_553 : EntryGood 553 := by
  unfold EntryGood
  rw [entry_553_checked]
  decide +kernel
theorem good_553 : Good (rowAt 553) := by
  rw [row_553]
  unfold Good
  decide +kernel

theorem entry_554_checked : entryAt 554 = entry_554 := by
  rw [entry_chunk_27 8 (by decide)]
  decide +kernel
theorem row_554 : rowAt 554 = data_554 := by
  rw [rowAt, dif_neg (by decide : ¬ 554 < 6), entry_554_checked]
  change forkRow [placeRow ⟨30, 6, 5, 4⟩ (rowAt 30), placeRow ⟨96, 7, 4, 5⟩ (rowAt 96), placeRow ⟨474, 0, 4, 5⟩ (rowAt 474)] = data_554
  rw [row_30, row_96, row_474]
  apply row_ext <;> decide +kernel
theorem entry_good_554 : EntryGood 554 := by
  unfold EntryGood
  rw [entry_554_checked]
  decide +kernel
theorem good_554 : Good (rowAt 554) := by
  rw [row_554]
  unfold Good
  decide +kernel

theorem entry_555_checked : entryAt 555 = entry_555 := by
  rw [entry_chunk_27 9 (by decide)]
  decide +kernel
theorem row_555 : rowAt 555 = data_555 := by
  rw [rowAt, dif_neg (by decide : ¬ 555 < 6), entry_555_checked]
  change forkRow [placeRow ⟨504, 5, 3, 5⟩ (rowAt 504), placeRow ⟨513, 0, 1, 5⟩ (rowAt 513), placeRow ⟨55, 0, 5, 4⟩ (rowAt 55), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨471, 1, 1, 5⟩ (rowAt 471)] = data_555
  rw [row_504, row_513, row_55, row_443, row_471]
  apply row_ext <;> decide +kernel
theorem entry_good_555 : EntryGood 555 := by
  unfold EntryGood
  rw [entry_555_checked]
  decide +kernel
theorem good_555 : Good (rowAt 555) := by
  rw [row_555]
  unfold Good
  decide +kernel


theorem block17_group01_piece00_correct : (rowAt 552 = data_552 ∧ Good (rowAt 552) ∧ EntryGood 552) ∧ (rowAt 553 = data_553 ∧ Good (rowAt 553) ∧ EntryGood 553) ∧ (rowAt 554 = data_554 ∧ Good (rowAt 554) ∧ EntryGood 554) ∧ (rowAt 555 = data_555 ∧ Good (rowAt 555) ∧ EntryGood 555) ∧ True := by
  exact ⟨⟨row_552, good_552, entry_good_552⟩, ⟨row_553, good_553, entry_good_553⟩, ⟨row_554, good_554, entry_good_554⟩, ⟨row_555, good_555, entry_good_555⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
