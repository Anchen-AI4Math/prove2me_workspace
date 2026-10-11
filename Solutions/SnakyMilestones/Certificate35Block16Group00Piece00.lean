import Definitions.Def_Snaky35Cache16
import Solutions.SnakyMilestones.Certificate35Part15
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_512_checked : entryAt 512 = entry_512 := by
  rw [entry_chunk_25 6 (by decide)]
  decide +kernel
theorem row_512 : rowAt 512 = data_512 := by
  rw [rowAt, dif_neg (by decide : ¬ 512 < 6), entry_512_checked]
  change forkRow [placeRow ⟨62, 0, 5, 4⟩ (rowAt 62), placeRow ⟨107, 0, 5, 4⟩ (rowAt 107), placeRow ⟨507, 0, 4, 6⟩ (rowAt 507)] = data_512
  rw [row_62, row_107, row_507]
  apply row_ext <;> decide +kernel
theorem entry_good_512 : EntryGood 512 := by
  unfold EntryGood
  rw [entry_512_checked]
  decide +kernel
theorem good_512 : Good (rowAt 512) := by
  rw [row_512]
  unfold Good
  decide +kernel

theorem entry_513_checked : entryAt 513 = entry_513 := by
  rw [entry_chunk_25 7 (by decide)]
  decide +kernel
theorem row_513 : rowAt 513 = data_513 := by
  rw [rowAt, dif_neg (by decide : ¬ 513 < 6), entry_513_checked]
  change forkRow [placeRow ⟨6, 4, 3, 4⟩ (rowAt 6), placeRow ⟨396, 0, 4, 5⟩ (rowAt 396)] = data_513
  rw [row_6, row_396]
  apply row_ext <;> decide +kernel
theorem entry_good_513 : EntryGood 513 := by
  unfold EntryGood
  rw [entry_513_checked]
  decide +kernel
theorem good_513 : Good (rowAt 513) := by
  rw [row_513]
  unfold Good
  decide +kernel

theorem entry_514_checked : entryAt 514 = entry_514 := by
  rw [entry_chunk_25 8 (by decide)]
  decide +kernel
theorem row_514 : rowAt 514 = data_514 := by
  rw [rowAt, dif_neg (by decide : ¬ 514 < 6), entry_514_checked]
  change forkRow [placeRow ⟨57, 0, 5, 4⟩ (rowAt 57), placeRow ⟨443, 4, 1, 5⟩ (rowAt 443), placeRow ⟨510, 0, 1, 5⟩ (rowAt 510)] = data_514
  rw [row_57, row_443, row_510]
  apply row_ext <;> decide +kernel
theorem entry_good_514 : EntryGood 514 := by
  unfold EntryGood
  rw [entry_514_checked]
  decide +kernel
theorem good_514 : Good (rowAt 514) := by
  rw [row_514]
  unfold Good
  decide +kernel

theorem entry_515_checked : entryAt 515 = entry_515 := by
  rw [entry_chunk_25 9 (by decide)]
  decide +kernel
theorem row_515 : rowAt 515 = data_515 := by
  rw [rowAt, dif_neg (by decide : ¬ 515 < 6), entry_515_checked]
  change forkRow [placeRow ⟨2, 6, 2, 4⟩ (rowAt 2), placeRow ⟨512, 1, 1, 5⟩ (rowAt 512)] = data_515
  rw [row_2, row_512]
  apply row_ext <;> decide +kernel
theorem entry_good_515 : EntryGood 515 := by
  unfold EntryGood
  rw [entry_515_checked]
  decide +kernel
theorem good_515 : Good (rowAt 515) := by
  rw [row_515]
  unfold Good
  decide +kernel


theorem block16_group00_piece00_correct : (rowAt 512 = data_512 ∧ Good (rowAt 512) ∧ EntryGood 512) ∧ (rowAt 513 = data_513 ∧ Good (rowAt 513) ∧ EntryGood 513) ∧ (rowAt 514 = data_514 ∧ Good (rowAt 514) ∧ EntryGood 514) ∧ (rowAt 515 = data_515 ∧ Good (rowAt 515) ∧ EntryGood 515) ∧ True := by
  exact ⟨⟨row_512, good_512, entry_good_512⟩, ⟨row_513, good_513, entry_good_513⟩, ⟨row_514, good_514, entry_good_514⟩, ⟨row_515, good_515, entry_good_515⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
