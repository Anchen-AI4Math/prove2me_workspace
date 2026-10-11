import Definitions.Def_Snaky35Cache04
import Solutions.SnakyMilestones.Certificate35Block04Group02
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_152_checked : entryAt 152 = entry_152 := by
  rw [entry_chunk_7 6 (by decide)]
  decide +kernel
theorem row_152 : rowAt 152 = data_152 := by
  rw [rowAt, dif_neg (by decide : ¬ 152 < 6), entry_152_checked]
  change forkRow [placeRow ⟨6, 3, 4, 5⟩ (rowAt 6), placeRow ⟨73, 1, 7, 4⟩ (rowAt 73)] = data_152
  rw [row_6, row_73]
  apply row_ext <;> decide +kernel
theorem entry_good_152 : EntryGood 152 := by
  unfold EntryGood
  rw [entry_152_checked]
  decide +kernel
theorem good_152 : Good (rowAt 152) := by
  rw [row_152]
  unfold Good
  decide +kernel

theorem entry_153_checked : entryAt 153 = entry_153 := by
  rw [entry_chunk_7 7 (by decide)]
  decide +kernel
theorem row_153 : rowAt 153 = data_153 := by
  rw [rowAt, dif_neg (by decide : ¬ 153 < 6), entry_153_checked]
  change forkRow [placeRow ⟨59, 4, 0, 4⟩ (rowAt 59), placeRow ⟨27, 0, 5, 4⟩ (rowAt 27)] = data_153
  rw [row_59, row_27]
  apply row_ext <;> decide +kernel
theorem entry_good_153 : EntryGood 153 := by
  unfold EntryGood
  rw [entry_153_checked]
  decide +kernel
theorem good_153 : Good (rowAt 153) := by
  rw [row_153]
  unfold Good
  decide +kernel

theorem entry_154_checked : entryAt 154 = entry_154 := by
  rw [entry_chunk_7 8 (by decide)]
  decide +kernel
theorem row_154 : rowAt 154 = data_154 := by
  rw [rowAt, dif_neg (by decide : ¬ 154 < 6), entry_154_checked]
  change forkRow [placeRow ⟨7, 6, 4, 3⟩ (rowAt 7), placeRow ⟨104, 0, 7, 5⟩ (rowAt 104)] = data_154
  rw [row_7, row_104]
  apply row_ext <;> decide +kernel
theorem entry_good_154 : EntryGood 154 := by
  unfold EntryGood
  rw [entry_154_checked]
  decide +kernel
theorem good_154 : Good (rowAt 154) := by
  rw [row_154]
  unfold Good
  decide +kernel

theorem entry_155_checked : entryAt 155 = entry_155 := by
  rw [entry_chunk_7 9 (by decide)]
  decide +kernel
theorem row_155 : rowAt 155 = data_155 := by
  rw [rowAt, dif_neg (by decide : ¬ 155 < 6), entry_155_checked]
  change forkRow [placeRow ⟨7, 1, 5, 4⟩ (rowAt 7), placeRow ⟨55, 3, 4, 5⟩ (rowAt 55)] = data_155
  rw [row_7, row_55]
  apply row_ext <;> decide +kernel
theorem entry_good_155 : EntryGood 155 := by
  unfold EntryGood
  rw [entry_155_checked]
  decide +kernel
theorem good_155 : Good (rowAt 155) := by
  rw [row_155]
  unfold Good
  decide +kernel


theorem block04_group03_piece00_correct : (rowAt 152 = data_152 ∧ Good (rowAt 152) ∧ EntryGood 152) ∧ (rowAt 153 = data_153 ∧ Good (rowAt 153) ∧ EntryGood 153) ∧ (rowAt 154 = data_154 ∧ Good (rowAt 154) ∧ EntryGood 154) ∧ (rowAt 155 = data_155 ∧ Good (rowAt 155) ∧ EntryGood 155) ∧ True := by
  exact ⟨⟨row_152, good_152, entry_good_152⟩, ⟨row_153, good_153, entry_good_153⟩, ⟨row_154, good_154, entry_good_154⟩, ⟨row_155, good_155, entry_good_155⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
