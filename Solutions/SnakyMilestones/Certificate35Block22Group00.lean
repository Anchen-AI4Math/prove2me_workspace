import Definitions.Def_Snaky35Cache22
import Solutions.SnakyMilestones.Certificate35Part21
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_615_checked : entryAt 615 = entry_615 := by
  rw [entry_chunk_30 9 (by decide)]
  decide +kernel
theorem row_615 : rowAt 615 = data_615 := by
  rw [rowAt, dif_neg (by decide : ¬ 615 < 6), entry_615_checked]
  change forkRow [placeRow ⟨602, 7, 6, 4⟩ (rowAt 602), placeRow ⟨614, 1, 4, 3⟩ (rowAt 614), placeRow ⟨533, 5, 6, 4⟩ (rowAt 533), placeRow ⟨590, 7, 6, 4⟩ (rowAt 590), placeRow ⟨611, 6, 3, 4⟩ (rowAt 611), placeRow ⟨587, 3, 3, 4⟩ (rowAt 587), placeRow ⟨601, 5, 6, 4⟩ (rowAt 601), placeRow ⟨406, 1, 6, 4⟩ (rowAt 406), placeRow ⟨591, 3, 3, 4⟩ (rowAt 591), placeRow ⟨586, 3, 3, 4⟩ (rowAt 586), placeRow ⟨584, 5, 6, 4⟩ (rowAt 584), placeRow ⟨406, 3, 3, 4⟩ (rowAt 406)] = data_615
  rw [row_602, row_614, row_533, row_590, row_611, row_587, row_601, row_406, row_591, row_586, row_584]
  apply row_ext <;> decide +kernel
theorem entry_good_615 : EntryGood 615 := by
  unfold EntryGood
  rw [entry_615_checked]
  decide +kernel
theorem good_615 : Good (rowAt 615) := by
  rw [row_615]
  unfold Good
  decide +kernel

#check row_615
theorem block22_group00_correct : (rowAt 615 = data_615 ∧ Good (rowAt 615) ∧ EntryGood 615) ∧ True := by
  exact ⟨⟨row_615, good_615, entry_good_615⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
