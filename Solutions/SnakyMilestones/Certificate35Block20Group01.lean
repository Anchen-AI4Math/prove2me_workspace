import Definitions.Def_Snaky35Cache20
import Solutions.SnakyMilestones.Certificate35Block20Group00
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_609_checked : entryAt 609 = entry_609 := by
  rw [entry_chunk_30 3 (by decide)]
  decide +kernel
theorem row_609 : rowAt 609 = data_609 := by
  rw [rowAt, dif_neg (by decide : ¬ 609 < 6), entry_609_checked]
  change forkRow [placeRow ⟨286, 4, 4, 5⟩ (rowAt 286), placeRow ⟨107, 3, 4, 5⟩ (rowAt 107), placeRow ⟨532, 4, 4, 5⟩ (rowAt 532), placeRow ⟨542, 0, 4, 5⟩ (rowAt 542), placeRow ⟨221, 3, 4, 5⟩ (rowAt 221), placeRow ⟨562, 4, 4, 5⟩ (rowAt 562), placeRow ⟨575, 4, 4, 5⟩ (rowAt 575), placeRow ⟨604, 1, 6, 4⟩ (rowAt 604)] = data_609
  rw [row_286, row_107, row_532, row_542, row_221, row_562, row_575, row_604]
  apply row_ext <;> decide +kernel
theorem entry_good_609 : EntryGood 609 := by
  unfold EntryGood
  rw [entry_609_checked]
  decide +kernel
theorem good_609 : Good (rowAt 609) := by
  rw [row_609]
  unfold Good
  decide +kernel

theorem block20_group01_correct : (rowAt 609 = data_609 ∧ Good (rowAt 609) ∧ EntryGood 609) ∧ True := by
  exact ⟨⟨row_609, good_609, entry_good_609⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
