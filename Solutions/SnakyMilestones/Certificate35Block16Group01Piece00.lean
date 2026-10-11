import Definitions.Def_Snaky35Cache16
import Solutions.SnakyMilestones.Certificate35Block16Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_520_checked : entryAt 520 = entry_520 := by
  rw [entry_chunk_25 14 (by decide)]
  decide +kernel
theorem row_520 : rowAt 520 = data_520 := by
  rw [rowAt, dif_neg (by decide : ¬ 520 < 6), entry_520_checked]
  change forkRow [placeRow ⟨254, 0, 2, 3⟩ (rowAt 254), placeRow ⟨200, 5, 6, 4⟩ (rowAt 200), placeRow ⟨271, 6, 5, 3⟩ (rowAt 271), placeRow ⟨215, 2, 5, 3⟩ (rowAt 215), placeRow ⟨252, 4, 2, 4⟩ (rowAt 252)] = data_520
  rw [row_254, row_200, row_271, row_215, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_520 : EntryGood 520 := by
  unfold EntryGood
  rw [entry_520_checked]
  decide +kernel
theorem good_520 : Good (rowAt 520) := by
  rw [row_520]
  unfold Good
  decide +kernel

theorem entry_521_checked : entryAt 521 = entry_521 := by
  rw [entry_chunk_25 15 (by decide)]
  decide +kernel
theorem row_521 : rowAt 521 = data_521 := by
  rw [rowAt, dif_neg (by decide : ¬ 521 < 6), entry_521_checked]
  change forkRow [placeRow ⟨492, 4, 5, 1⟩ (rowAt 492), placeRow ⟨2, 7, 4, 2⟩ (rowAt 2)] = data_521
  rw [row_492, row_2]
  apply row_ext <;> decide +kernel
theorem entry_good_521 : EntryGood 521 := by
  unfold EntryGood
  rw [entry_521_checked]
  decide +kernel
theorem good_521 : Good (rowAt 521) := by
  rw [row_521]
  unfold Good
  decide +kernel

theorem entry_522_checked : entryAt 522 = entry_522 := by
  rw [entry_chunk_25 16 (by decide)]
  decide +kernel
theorem row_522 : rowAt 522 = data_522 := by
  rw [rowAt, dif_neg (by decide : ¬ 522 < 6), entry_522_checked]
  change forkRow [placeRow ⟨176, 3, 4, 6⟩ (rowAt 176), placeRow ⟨338, 2, 3, 3⟩ (rowAt 338), placeRow ⟨252, 1, 4, 6⟩ (rowAt 252)] = data_522
  rw [row_176, row_338, row_252]
  apply row_ext <;> decide +kernel
theorem entry_good_522 : EntryGood 522 := by
  unfold EntryGood
  rw [entry_522_checked]
  decide +kernel
theorem good_522 : Good (rowAt 522) := by
  rw [row_522]
  unfold Good
  decide +kernel

theorem entry_523_checked : entryAt 523 = entry_523 := by
  rw [entry_chunk_25 17 (by decide)]
  decide +kernel
theorem row_523 : rowAt 523 = data_523 := by
  rw [rowAt, dif_neg (by decide : ¬ 523 < 6), entry_523_checked]
  change forkRow [placeRow ⟨303, 1, 5, 4⟩ (rowAt 303), placeRow ⟨25, 4, 1, 5⟩ (rowAt 25), placeRow ⟨107, 2, 5, 4⟩ (rowAt 107), placeRow ⟨511, 4, 1, 6⟩ (rowAt 511)] = data_523
  rw [row_303, row_25, row_107, row_511]
  apply row_ext <;> decide +kernel
theorem entry_good_523 : EntryGood 523 := by
  unfold EntryGood
  rw [entry_523_checked]
  decide +kernel
theorem good_523 : Good (rowAt 523) := by
  rw [row_523]
  unfold Good
  decide +kernel


theorem block16_group01_piece00_correct : (rowAt 520 = data_520 ∧ Good (rowAt 520) ∧ EntryGood 520) ∧ (rowAt 521 = data_521 ∧ Good (rowAt 521) ∧ EntryGood 521) ∧ (rowAt 522 = data_522 ∧ Good (rowAt 522) ∧ EntryGood 522) ∧ (rowAt 523 = data_523 ∧ Good (rowAt 523) ∧ EntryGood 523) ∧ True := by
  exact ⟨⟨row_520, good_520, entry_good_520⟩, ⟨row_521, good_521, entry_good_521⟩, ⟨row_522, good_522, entry_good_522⟩, ⟨row_523, good_523, entry_good_523⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
