import Definitions.Def_Snaky35Cache15
import Solutions.SnakyMilestones.Certificate35Block15Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_504_checked : entryAt 504 = entry_504 := by
  rw [entry_chunk_24 18 (by decide)]
  decide +kernel
theorem row_504 : rowAt 504 = data_504 := by
  rw [rowAt, dif_neg (by decide : ¬ 504 < 6), entry_504_checked]
  change forkRow [placeRow ⟨381, 0, 3, 4⟩ (rowAt 381), placeRow ⟨310, 4, 4, 5⟩ (rowAt 310), placeRow ⟨159, 0, 5, 6⟩ (rowAt 159), placeRow ⟨351, 4, 3, 4⟩ (rowAt 351), placeRow ⟨496, 0, 3, 4⟩ (rowAt 496)] = data_504
  rw [row_381, row_310, row_159, row_351, row_496]
  apply row_ext <;> decide +kernel
theorem entry_good_504 : EntryGood 504 := by
  unfold EntryGood
  rw [entry_504_checked]
  decide +kernel
theorem good_504 : Good (rowAt 504) := by
  rw [row_504]
  unfold Good
  decide +kernel

theorem entry_505_checked : entryAt 505 = entry_505 := by
  rw [entry_chunk_24 19 (by decide)]
  decide +kernel
theorem row_505 : rowAt 505 = data_505 := by
  rw [rowAt, dif_neg (by decide : ¬ 505 < 6), entry_505_checked]
  change forkRow [placeRow ⟨173, 1, 4, 5⟩ (rowAt 173), placeRow ⟨499, 0, 5, 4⟩ (rowAt 499), placeRow ⟨183, 1, 4, 5⟩ (rowAt 183), placeRow ⟨282, 1, 4, 5⟩ (rowAt 282)] = data_505
  rw [row_173, row_499, row_183, row_282]
  apply row_ext <;> decide +kernel
theorem entry_good_505 : EntryGood 505 := by
  unfold EntryGood
  rw [entry_505_checked]
  decide +kernel
theorem good_505 : Good (rowAt 505) := by
  rw [row_505]
  unfold Good
  decide +kernel

theorem entry_506_checked : entryAt 506 = entry_506 := by
  rw [entry_chunk_25 0 (by decide)]
  decide +kernel
theorem row_506 : rowAt 506 = data_506 := by
  rw [rowAt, dif_neg (by decide : ¬ 506 < 6), entry_506_checked]
  change forkRow [placeRow ⟨99, 0, 4, 5⟩ (rowAt 99), placeRow ⟨200, 7, 1, 4⟩ (rowAt 200), placeRow ⟨318, 5, 5, 4⟩ (rowAt 318), placeRow ⟨173, 0, 5, 4⟩ (rowAt 173)] = data_506
  rw [row_99, row_200, row_318, row_173]
  apply row_ext <;> decide +kernel
theorem entry_good_506 : EntryGood 506 := by
  unfold EntryGood
  rw [entry_506_checked]
  decide +kernel
theorem good_506 : Good (rowAt 506) := by
  rw [row_506]
  unfold Good
  decide +kernel

theorem entry_507_checked : entryAt 507 = entry_507 := by
  rw [entry_chunk_25 1 (by decide)]
  decide +kernel
theorem row_507 : rowAt 507 = data_507 := by
  rw [rowAt, dif_neg (by decide : ¬ 507 < 6), entry_507_checked]
  change forkRow [placeRow ⟨151, 0, 2, 4⟩ (rowAt 151), placeRow ⟨33, 3, 4, 3⟩ (rowAt 33), placeRow ⟨481, 0, 5, 4⟩ (rowAt 481)] = data_507
  rw [row_151, row_33, row_481]
  apply row_ext <;> decide +kernel
theorem entry_good_507 : EntryGood 507 := by
  unfold EntryGood
  rw [entry_507_checked]
  decide +kernel
theorem good_507 : Good (rowAt 507) := by
  rw [row_507]
  unfold Good
  decide +kernel


theorem block15_group03_piece00_correct : (rowAt 504 = data_504 ∧ Good (rowAt 504) ∧ EntryGood 504) ∧ (rowAt 505 = data_505 ∧ Good (rowAt 505) ∧ EntryGood 505) ∧ (rowAt 506 = data_506 ∧ Good (rowAt 506) ∧ EntryGood 506) ∧ (rowAt 507 = data_507 ∧ Good (rowAt 507) ∧ EntryGood 507) ∧ True := by
  exact ⟨⟨row_504, good_504, entry_good_504⟩, ⟨row_505, good_505, entry_good_505⟩, ⟨row_506, good_506, entry_good_506⟩, ⟨row_507, good_507, entry_good_507⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
