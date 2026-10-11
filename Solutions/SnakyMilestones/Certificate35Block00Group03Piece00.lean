import Definitions.Def_Snaky35Cache00
import Solutions.SnakyMilestones.Certificate35Block00Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_24_checked : entryAt 24 = entry_24 := by
  rw [entry_chunk_0 18 (by decide)]
  decide +kernel
theorem row_24 : rowAt 24 = data_24 := by
  rw [rowAt, dif_neg (by decide : ¬ 24 < 6), entry_24_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨17, 0, 5, 4⟩ (rowAt 17)] = data_24
  rw [row_0, row_17]
  apply row_ext <;> decide +kernel
theorem entry_good_24 : EntryGood 24 := by
  unfold EntryGood
  rw [entry_24_checked]
  decide +kernel
theorem good_24 : Good (rowAt 24) := by
  rw [row_24]
  unfold Good
  decide +kernel

theorem entry_25_checked : entryAt 25 = entry_25 := by
  rw [entry_chunk_0 19 (by decide)]
  decide +kernel
theorem row_25 : rowAt 25 = data_25 := by
  rw [rowAt, dif_neg (by decide : ¬ 25 < 6), entry_25_checked]
  change forkRow [placeRow ⟨0, 0, 0, 3⟩ (rowAt 0), placeRow ⟨14, 0, 5, 4⟩ (rowAt 14)] = data_25
  rw [row_0, row_14]
  apply row_ext <;> decide +kernel
theorem entry_good_25 : EntryGood 25 := by
  unfold EntryGood
  rw [entry_25_checked]
  decide +kernel
theorem good_25 : Good (rowAt 25) := by
  rw [row_25]
  unfold Good
  decide +kernel


theorem block00_group03_piece00_correct : (rowAt 24 = data_24 ∧ Good (rowAt 24) ∧ EntryGood 24) ∧ (rowAt 25 = data_25 ∧ Good (rowAt 25) ∧ EntryGood 25) ∧ True := by
  exact ⟨⟨row_24, good_24, entry_good_24⟩, ⟨row_25, good_25, entry_good_25⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
