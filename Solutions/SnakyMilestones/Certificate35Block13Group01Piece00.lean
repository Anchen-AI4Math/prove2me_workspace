import Definitions.Def_Snaky35Cache13
import Solutions.SnakyMilestones.Certificate35Block13Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_424_checked : entryAt 424 = entry_424 := by
  rw [entry_chunk_20 18 (by decide)]
  decide +kernel
theorem row_424 : rowAt 424 = data_424 := by
  rw [rowAt, dif_neg (by decide : ¬ 424 < 6), entry_424_checked]
  change forkRow [placeRow ⟨55, 1, 4, 5⟩ (rowAt 55), placeRow ⟨394, 0, 6, 4⟩ (rowAt 394), placeRow ⟨216, 3, 4, 5⟩ (rowAt 216)] = data_424
  rw [row_55, row_394, row_216]
  apply row_ext <;> decide +kernel
theorem entry_good_424 : EntryGood 424 := by
  unfold EntryGood
  rw [entry_424_checked]
  decide +kernel
theorem good_424 : Good (rowAt 424) := by
  rw [row_424]
  unfold Good
  decide +kernel

theorem entry_425_checked : entryAt 425 = entry_425 := by
  rw [entry_chunk_20 19 (by decide)]
  decide +kernel
theorem row_425 : rowAt 425 = data_425 := by
  rw [rowAt, dif_neg (by decide : ¬ 425 < 6), entry_425_checked]
  change forkRow [placeRow ⟨386, 0, 5, 4⟩ (rowAt 386), placeRow ⟨226, 1, 4, 5⟩ (rowAt 226), placeRow ⟨378, 4, 2, 4⟩ (rowAt 378), placeRow ⟨378, 0, 5, 4⟩ (rowAt 378), placeRow ⟨386, 4, 2, 4⟩ (rowAt 386)] = data_425
  rw [row_386, row_226, row_378]
  apply row_ext <;> decide +kernel
theorem entry_good_425 : EntryGood 425 := by
  unfold EntryGood
  rw [entry_425_checked]
  decide +kernel
theorem good_425 : Good (rowAt 425) := by
  rw [row_425]
  unfold Good
  decide +kernel

theorem entry_426_checked : entryAt 426 = entry_426 := by
  rw [entry_chunk_21 0 (by decide)]
  decide +kernel
theorem row_426 : rowAt 426 = data_426 := by
  rw [rowAt, dif_neg (by decide : ¬ 426 < 6), entry_426_checked]
  change forkRow [placeRow ⟨300, 6, 4, 1⟩ (rowAt 300), placeRow ⟨252, 1, 4, 5⟩ (rowAt 252), placeRow ⟨397, 0, 3, 4⟩ (rowAt 397), placeRow ⟨291, 1, 4, 1⟩ (rowAt 291), placeRow ⟨328, 0, 4, 5⟩ (rowAt 328), placeRow ⟨319, 1, 3, 5⟩ (rowAt 319)] = data_426
  rw [row_300, row_252, row_397, row_291, row_328, row_319]
  apply row_ext <;> decide +kernel
theorem entry_good_426 : EntryGood 426 := by
  unfold EntryGood
  rw [entry_426_checked]
  decide +kernel
theorem good_426 : Good (rowAt 426) := by
  rw [row_426]
  unfold Good
  decide +kernel

theorem entry_427_checked : entryAt 427 = entry_427 := by
  rw [entry_chunk_21 1 (by decide)]
  decide +kernel
theorem row_427 : rowAt 427 = data_427 := by
  rw [rowAt, dif_neg (by decide : ¬ 427 < 6), entry_427_checked]
  change forkRow [placeRow ⟨45, 1, 3, 7⟩ (rowAt 45), placeRow ⟨106, 6, 2, 3⟩ (rowAt 106), placeRow ⟨420, 1, 6, 4⟩ (rowAt 420)] = data_427
  rw [row_45, row_106, row_420]
  apply row_ext <;> decide +kernel
theorem entry_good_427 : EntryGood 427 := by
  unfold EntryGood
  rw [entry_427_checked]
  decide +kernel
theorem good_427 : Good (rowAt 427) := by
  rw [row_427]
  unfold Good
  decide +kernel


theorem block13_group01_piece00_correct : (rowAt 424 = data_424 ∧ Good (rowAt 424) ∧ EntryGood 424) ∧ (rowAt 425 = data_425 ∧ Good (rowAt 425) ∧ EntryGood 425) ∧ (rowAt 426 = data_426 ∧ Good (rowAt 426) ∧ EntryGood 426) ∧ (rowAt 427 = data_427 ∧ Good (rowAt 427) ∧ EntryGood 427) ∧ True := by
  exact ⟨⟨row_424, good_424, entry_good_424⟩, ⟨row_425, good_425, entry_good_425⟩, ⟨row_426, good_426, entry_good_426⟩, ⟨row_427, good_427, entry_good_427⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
