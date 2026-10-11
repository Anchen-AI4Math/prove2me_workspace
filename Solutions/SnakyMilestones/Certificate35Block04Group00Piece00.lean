import Definitions.Def_Snaky35Cache04
import Solutions.SnakyMilestones.Certificate35Part03
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace OAI.SnakyCertificate.MilestoneChecks
open OAI.SnakyCertificate
theorem entry_128_checked : entryAt 128 = entry_128 := by
  rw [entry_chunk_6 2 (by decide)]
  decide +kernel
theorem row_128 : rowAt 128 = data_128 := by
  rw [rowAt, dif_neg (by decide : ¬ 128 < 6), entry_128_checked]
  change forkRow [placeRow ⟨9, 6, 1, 5⟩ (rowAt 9), placeRow ⟨57, 0, 6, 5⟩ (rowAt 57)] = data_128
  rw [row_9, row_57]
  apply row_ext <;> decide +kernel
theorem entry_good_128 : EntryGood 128 := by
  unfold EntryGood
  rw [entry_128_checked]
  decide +kernel
theorem good_128 : Good (rowAt 128) := by
  rw [row_128]
  unfold Good
  decide +kernel

theorem entry_129_checked : entryAt 129 = entry_129 := by
  rw [entry_chunk_6 3 (by decide)]
  decide +kernel
theorem row_129 : rowAt 129 = data_129 := by
  rw [rowAt, dif_neg (by decide : ¬ 129 < 6), entry_129_checked]
  change forkRow [placeRow ⟨6, 4, 2, 5⟩ (rowAt 6), placeRow ⟨58, 1, 3, 6⟩ (rowAt 58)] = data_129
  rw [row_6, row_58]
  apply row_ext <;> decide +kernel
theorem entry_good_129 : EntryGood 129 := by
  unfold EntryGood
  rw [entry_129_checked]
  decide +kernel
theorem good_129 : Good (rowAt 129) := by
  rw [row_129]
  unfold Good
  decide +kernel

theorem entry_130_checked : entryAt 130 = entry_130 := by
  rw [entry_chunk_6 4 (by decide)]
  decide +kernel
theorem row_130 : rowAt 130 = data_130 := by
  rw [rowAt, dif_neg (by decide : ¬ 130 < 6), entry_130_checked]
  change forkRow [placeRow ⟨6, 1, 4, 5⟩ (rowAt 6), placeRow ⟨60, 0, 5, 4⟩ (rowAt 60)] = data_130
  rw [row_6, row_60]
  apply row_ext <;> decide +kernel
theorem entry_good_130 : EntryGood 130 := by
  unfold EntryGood
  rw [entry_130_checked]
  decide +kernel
theorem good_130 : Good (rowAt 130) := by
  rw [row_130]
  unfold Good
  decide +kernel

theorem entry_131_checked : entryAt 131 = entry_131 := by
  rw [entry_chunk_6 5 (by decide)]
  decide +kernel
theorem row_131 : rowAt 131 = data_131 := by
  rw [rowAt, dif_neg (by decide : ¬ 131 < 6), entry_131_checked]
  change forkRow [placeRow ⟨45, 3, 4, 5⟩ (rowAt 45), placeRow ⟨7, 1, 5, 4⟩ (rowAt 7)] = data_131
  rw [row_45, row_7]
  apply row_ext <;> decide +kernel
theorem entry_good_131 : EntryGood 131 := by
  unfold EntryGood
  rw [entry_131_checked]
  decide +kernel
theorem good_131 : Good (rowAt 131) := by
  rw [row_131]
  unfold Good
  decide +kernel


theorem block04_group00_piece00_correct : (rowAt 128 = data_128 ∧ Good (rowAt 128) ∧ EntryGood 128) ∧ (rowAt 129 = data_129 ∧ Good (rowAt 129) ∧ EntryGood 129) ∧ (rowAt 130 = data_130 ∧ Good (rowAt 130) ∧ EntryGood 130) ∧ (rowAt 131 = data_131 ∧ Good (rowAt 131) ∧ EntryGood 131) ∧ True := by
  exact ⟨⟨row_128, good_128, entry_good_128⟩, ⟨row_129, good_129, entry_good_129⟩, ⟨row_130, good_130, entry_good_130⟩, ⟨row_131, good_131, entry_good_131⟩, trivial⟩
end OAI.SnakyCertificate.MilestoneChecks
